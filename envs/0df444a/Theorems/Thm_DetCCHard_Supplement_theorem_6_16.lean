-- Prove2me | Theorems.Thm_DetCCHard_Supplement_theorem_6_16
-- name    : DetCCHard.Supplement.theorem_6_16
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T04:59:31.719486+00:00
-- url     : https://prove2.me/theorems/4d81cea9-410b-41dd-873e-6dd0e1db3d5e
-- title:
--   Theorem 6.16 — under (H1)–(H4): $D(W) = C + \log w$, $\mathcal P(W; \theta, C + \log w - 1)$, and near-full restrictions cost $\ge C + \log w$
-- statement:
--   Assume the common hypotheses of §6.5, with $H_1, H_2, C$ as in (1) and $H_1, H_2 \ge 2$:
--
--   1. **(H1)** $\mathcal P(A; x, H_1)$, $\mathcal P(R_{\mathrm{temp}}; x, H_2)$ and $\mathcal P(N_{\mathrm{ref}}; x, C - 1)$;
--   2. **(H2)** $N$ has exact cost $C$, including on every restriction retaining $1 - \eta$ of each input set's total weight;
--   3. **(H3)** the weights on $S$ are exactly 8192-wise independent with the $J$ marginal, the bin tuple in $\Omega$ is exactly 8192-wise independent with the $J_2$ marginal, and the tuple list of $U = I_w(N)$ combines three mutually independent label sequences (type/bin/item labels, base labels with the $X$ weights, template labels with the $S$ weights), each exactly 8192-wise independent across the $w$ copies;
--   4. **(H4)** the numerical bounds (10).
--
--   Then, for $W = U^{\mathsf T}$,
--   $$
--   D(W) = C + \log w, \qquad \mathcal P(W; \theta, C + \log w - 1),
--   $$
--   and every restriction of $W$ retaining row weight at least $\theta$ and column weight at least $1 - \delta_U$ has cost at least $C + \log w$.
--
--   These are the two inputs of the restoration step (Theorems 6.17 and 7.2), which recovers the missing bit of the deletion bounds.
--
--   **Formalization Note** Stated for the list-parametrized construction with $U$ on the combined list of three label sequences, and the parameters of Definition 6.1: $s \ge 4$ dyadic, $\rho = 2^{-L}$ with $n \le \rho^{-1}$ and $\rho \le s^{-4}$, $q_2 = s^2/\rho$, $w = s^8$, $x = \rho^8$, $\eta = s^{-2}$, $\theta = (512 s^{24})^{-1}$, $\delta_U = \eta/(16w)$. All lists have positive normalized weights.
--
--   Differences from the source:
--   - generalization: the construction of Definition 6.2 or Definition 8.3 → the list-parametrized construction with any lists satisfying (H1)–(H4) (any positive normalized Γ-list and Ω-tail list); reason: both constructions are instances; §6.5 states that only (H1)–(H4) are used
--   - generalization: the recipe of Definition 6.1, including s ≥ s₀ → the recipe without s ≥ s₀; (10) is assumed as (H4); reason: s₀ is the constant making (10) hold
--   - generalization: a source graph of Theorem 5.2 with its constants Δ, γ → any graph and any Δ ≥ 1, γ > 0 entering (10); reason: §6.5 uses only (H1)–(H4); the graphs of Theorem 5.2 are a special case
--   - encoding: the tuple weights of U arise from three mutually independent label sequences combined coordinatewise → U is the interlace on combineH3 T1 T2 T3 (triples of labels, product weights); reason: the paper's construction of that list (Definition 8.3, p.36)
--   - encoding: positions of γ, blocks and π_α(i) → Fin (s − 2) ⊕ Fin (s + 1), 0-based; reason: bijective reindexing
-- source:
--   Gaspers–He–Mackenzie, NP-Hardness and Additive Inapproximability of Deterministic Communication Complexity, arXiv:2508.05597 (held version, sha256 ad552d13…), Theorem 6.16, p.30 (common hypotheses (H1)–(H4), §6.5, p.27)

import Mathlib
import Definitions.Def_DetCCHard_IsWeight
import Definitions.Def_DetCCHard_commCost
import Definitions.Def_DetCCHard_DeletionBounds
import Definitions.Def_DetCCHard_TupleList
import Definitions.Def_DetCCHard_interlaceOn
import Definitions.Def_DetCCHard_realRank
import Definitions.Def_DetCCHard_SrcGraph
import Definitions.Def_DetCCHard_pow2
import Definitions.Def_DetCCHard_Item
import Definitions.Def_DetCCHard_WMat
import Definitions.Def_DetCCHard_Supplement_RawList
import Definitions.Def_DetCCHard_Supplement_SrcData
import Definitions.Def_DetCCHard_Supplement_Ineq10

namespace DetCCHard.Supplement

open DetCCHard

/-- **Theorem 6.16 (Lower bounds for `W`)** (Gaspers–He–Mackenzie, arXiv:2508.05597, held version sha256 ad552d13…a4a03, Theorem 6.16, p.30, under the common
hypotheses (H1)–(H4) of §6.5, p.27). Under the common hypotheses of Section 6.5,
`D(W) = C + log w` and `P(W; θ, C + log w − 1)`. Every restriction of `W` retaining row weight at
least `θ` and column weight at least `1 − δ_U` has cost at least `C + log w`.

The common hypotheses, with `H₁`, `H₂`, `C` as in (1) and `H₁, H₂ ≥ 2`:
(H1) `P(A; x, H₁)`, `P(R_temp; x, H₂)` and `P(N_ref; x, C − 1)`;
(H2) `N` has exact cost `C`, including on every restriction retaining `1 − η` of each input set's
total weight;
(H3) the weights on `S` are exactly 8192-wise independent with the `J` marginal, the bin tuple in
`Ω` is exactly 8192-wise independent with the `J₂` marginal, and the tuple list of `U` arises from
three mutually independent label sequences (type/bin/item labels, base labels with the `X`
weights, template labels with the `S` weights), each exactly 8192-wise independent across the
`w` copies, combined coordinatewise;
(H4) the numerical bounds (10).

**Formalization Note** The construction is the list-parametrized source construction (`SrcData`)
with `U = I_w(N)` on the combined list `combineH3 T1 T2 T3` and `W = Uᵀ`. The parameters are
those of Definition 6.1: `s ≥ 4` dyadic, `ρ = 2^{-L}` with `n ≤ ρ^{-1}`, `ρ ≤ s^{-4}`,
`q₂ = s²/ρ` (equal to the construction's `q₀·2^t`), `w = s⁸`, `x = ρ⁸`, `η = s^{-2}`,
`θ = (512 s^{24})^{-1}`, `δ_U = η/(16w)`; `Δ ≥ 1`, `γ > 0` are the graph-promise constants in (10).
`W` has rows the labels of the combined list (weights their product) and columns
`[w] × (Ω ⊔ D)` (weights those of `N`'s rows divided by `w`). All lists have positive normalized
weights. -/
theorem theorem_6_16 (Δ : ℕ) (γ : ℚ) (hΔ : 1 ≤ Δ) (hγ : 0 < γ) (D : SrcData) (L : ℕ)
    (hs : ∃ a : ℕ, D.s = 2 ^ a) (hs4 : 4 ≤ D.s) (hn : D.G.n ≤ 2 ^ L) (hρ : D.s ^ 4 ≤ 2 ^ L)
    (hq : D.q = D.s ^ 2 * 2 ^ L)
    (hΓ : IsWeight D.TΓ.ν) (hΩ : IsWeight D.TΩ.ν) (hSw : IsWeight D.TS.ν) (hBw : IsWeight D.TB.ν)
    (T1 : RawList D.TypeLab (Fin (D.s ^ 8))) (T2 : RawList D.R.X (Fin (D.s ^ 8)))
    (T3 : RawList D.TS.L (Fin (D.s ^ 8)))
    (hH1H2 : 2 ≤ costH1 (Dcost D.R.entry) D.s ∧ 2 ≤ costH2 (Dcost D.R.entry) D.s D.q)
    (hH1 : D.TemplateDeletionBounds L)
    (hH2 : D.SourceHard (costC (Dcost D.R.entry) D.s D.q) (etaOf D.s))
    (hH3S : ExactlyIndepW D.TS.ν D.TS.z 8192 (jWt D.R D.s))
    (hH3B : ExactlyIndepW D.TB.ν D.TB.z 8192 (j2Wt D.TΓ D.q))
    (hH3U : D.H3Lists T1 T2 T3)
    (hH4 : Ineq10 Δ γ D.G D.s L) :
    let C := costC (Dcost D.R.entry) D.s D.q
    let w := D.s ^ 8
    let TU := D.combineH3 T1 T2 T3
    Dcost (D.W TU) = C + Nat.log 2 w ∧
      DeletionBounds (D.W TU) TU.ν (interlaceRowWt D.NWt w) (thetaOf D.s)
        ((C + Nat.log 2 w : ℕ) - 1 : ℤ) ∧
      ∀ (A : Set TU.L) (B : Set (Fin w × D.NRow)), thetaOf D.s ≤ (wt TU.ν A : ℝ) →
        1 - deltaUOf D.s ≤ (wt (interlaceRowWt D.NWt w) B : ℝ) →
        C + Nat.log 2 w ≤ commCost (D.W TU) A B := by sorry

end DetCCHard.Supplement
