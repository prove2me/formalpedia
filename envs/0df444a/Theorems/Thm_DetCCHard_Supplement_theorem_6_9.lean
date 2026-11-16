-- Prove2me | Theorems.Thm_DetCCHard_Supplement_theorem_6_9
-- name    : DetCCHard.Supplement.theorem_6_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T04:58:34.76375+00:00
-- url     : https://prove2.me/theorems/31a871ea-4557-4c2d-a0c4-695001acc200
-- title:
--   Theorem 6.9 — source hardness after deletion: $D(N) = C$ and restrictions keeping $1 - \eta$ of each input set cost $\ge C$
-- statement:
--   Use the source construction of Definition 6.2 (full products) or Definition 8.3 (explicit lists) with a NO graph, $D(R) = d \ge 3$, and $H_1, H_2, C, x_{\mathrm{cap}}$ as in (1). Suppose:
--
--   1. the template-layer deletion bounds $\mathcal P(A; x, H_1)$, $\mathcal P(R_{\mathrm{temp}}; x, H_2)$, $\mathcal P(N_{\mathrm{ref}}; x, C - 1)$ and the collision bound of Lemma 6.6 hold;
--   2. the numerical inequalities (10) of Lemma F.1 hold;
--   3. the weights on $S$ are exactly 8-wise independent with the prescribed weights on $J$ as marginal;
--   4. the bin tuple $(j_1, \dots, j_s)$ of the $\Omega$-inputs is exactly 8-wise independent with the prescribed $J_2$ marginal.
--
--   Then
--   $$
--   D(N) = C,
--   $$
--   and every restriction of $N$ retaining at least $1 - \eta$ of each input set's total weight has cost at least $C$. In either case of Theorem 5.3 with $\mathcal P(R; \rho, d)$, these hypotheses hold (Lemma 6.6, Lemma F.1 and the exact independence of the constructed weights).
--
--   This is the NO-case lower bound for the source matrix $N$, robust under the small deletions a protocol prefix can cause; it feeds hypothesis $(H2)$ of Theorem 6.16.
--
--   **Formalization Note** The first conjunct is stated for the list-parametrized construction with any lists meeting the hypotheses, with the parameters of Definition 6.1 ($s \ge 4$ dyadic, $\rho = 2^{-L}$, $n \le \rho^{-1}$, $\rho \le s^{-4}$, $q_2 = s^2/\rho$, $x = \rho^8$, $\eta = s^{-2}$). The second and third conjuncts are the last sentence, for the full-product parameters of Lemma F.2 (graphs above a cutoff $n_0$) and the explicit parameters of Lemma F.3 (dyadic $s \ge s_0$ with $s^4 \ge n$, exactly 8192-wise independent lists, $\Omega$-tails induced by the Γ-list); they also assert $\rho \le s^{-4}$ (resp. that $q_2$ is a dyadic multiple of $q_0$).
--
--   Differences from the source:
--   - generalization: the construction of Definition 6.2 or Definition 8.3 → the list-parametrized construction with any lists satisfying the hypotheses (any positive normalized Γ-list and Ω-tail list); reason: both constructions are instances; the hypotheses list everything the proof uses
--   - generalization: the recipe of Definition 6.1, including s ≥ s₀ (Lemma F.1) → the recipe without s ≥ s₀; the inequalities (10) are assumed instead; reason: s₀ is the constant making (10) hold, and (10) is a hypothesis
--   - generalization: the fixed constants Δ, γ of Theorem 5.2 → every Δ ≥ 1 and every rational γ > 0, with the cutoffs chosen after them; reason: the pair of Theorem 5.2 is a special case
--   - generalization: last sentence, explicit case: the s of Lemma F.3 and the Code8192 lists → every dyadic s ≥ s₀ with s⁴ ≥ n and any exactly 8192-wise independent lists with the prescribed marginals; reason: Lemma F.3 holds for every such s; the Code8192 lists are such lists
--   - reading: "these hypotheses follow" (last sentence) → the hypotheses of the first conjunct are asserted to hold in each case of Theorem 5.3 with P(R; ρ, d); reason: literal reading; with the first conjunct it gives the conclusion
--   - encoding: positions of γ, blocks and π_α(i) → Fin (s − 2) ⊕ Fin (s + 1), 0-based; reason: bijective reindexing
--   - encoding: n must exceed an effectively computable constant (Lemma F.2) → ∃ n₀ with n₀ < n; reason: same statement; effectivity is not formalized
-- source:
--   Gaspers–He–Mackenzie, NP-Hardness and Additive Inapproximability of Deterministic Communication Complexity, arXiv:2508.05597 (held version, sha256 ad552d13…), Theorem 6.9, p.24

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

/-- **Theorem 6.9 (Source hardness after deletion)** (Gaspers–He–Mackenzie, arXiv:2508.05597, held version sha256 ad552d13…a4a03, Theorem 6.9, p.24). Use either the
full-product construction of Definition 6.2 or the explicit-list construction of Definition 8.3,
with a NO graph and `D(R) = d ≥ 3`, and define `H₁`, `H₂`, `C`, `x_cap` by (1). Suppose the deletion
bounds and the collision bound stated in Lemma 6.6 hold. Assume the numerical inequalities (10) of
Lemma F.1, that the weights on `S` give exact 8-wise independence with the prescribed weights on
`J` as marginal, and that the bin tuple `(j₁, …, j_s)` of the `Ω`-inputs has exactly 8-wise
independent weights with the prescribed `J₂` marginal. Then `D(N) = C`, and every restriction
retaining at least `1 − η` of each input set's total weight has cost at least `C`. In either case of
Theorem 5.3 with `P(R; ρ, d)`, these hypotheses follow from Lemma 6.6, Lemma F.1, and the exact
independence of the constructed weights.

**Formalization Note** The first conjunct is the conditional statement, for the source construction
parametrized by lists (`SrcData`) with any lists satisfying the hypotheses, which covers both
Definition 6.2 and Definition 8.3. The parameters are those of Definition 6.1: `s ≥ 4` dyadic,
`ρ = 2^{-L}` with `n ≤ ρ^{-1}` and `ρ ≤ s^{-4}`, `q₂ = s²/ρ` (equal to the construction's
`q₀·2^t`), `x = ρ⁸`, `η = s^{-2}`. A NO graph is a graph of the shape of Theorem 5.2 (constants
`Δ ≥ 1`, `γ > 0`) every 3-coloring of which has `γ|E|` monochromatic edge occurrences. The second
conjunct is the last sentence in the full-product case (Lemma F.2: `L = ⌈log n⌉`,
`s = pow2(2^{16}(L + 1))`, `q₂ = s² 2^L`, `n` above a cutoff `n₀`), the third in the explicit case
(Lemma F.3: dyadic `s ≥ s₀` with `s⁴ ≥ n`, `ρ = s^{-4}`, `q₂ = s⁶`, exactly 8192-wise independent
lists, `Ω`-tails induced by the Γ-list). Both cases also assert that `q₂` is a dyadic multiple of
`q₀` and `ρ ≤ s^{-4}`. -/
theorem theorem_6_9 :
    (∀ (Δ : ℕ) (γ : ℚ) (D : SrcData) (L : ℕ), 1 ≤ Δ → 0 < γ → IsShape Δ D.G → IsNo γ D.G →
      (∃ a : ℕ, D.s = 2 ^ a) → 4 ≤ D.s → D.G.n ≤ 2 ^ L → D.s ^ 4 ≤ 2 ^ L →
      D.q = D.s ^ 2 * 2 ^ L →
      IsWeight D.TΓ.ν → IsWeight D.TΩ.ν → IsWeight D.TS.ν → IsWeight D.TB.ν →
      3 ≤ Dcost D.R.entry →
      D.TemplateDeletionBounds L → D.CollisionBound L → Ineq10 Δ γ D.G D.s L →
      ExactlyIndepW D.TS.ν D.TS.z 8 (jWt D.R D.s) →
      ExactlyIndepW D.TB.ν D.TB.z 8 (j2Wt D.TΓ D.q) →
      D.SourceHard (costC (Dcost D.R.entry) D.s D.q) (etaOf D.s)) ∧
    (∀ Δ : ℕ, 1 ≤ Δ → ∀ γ : ℚ, 0 < γ → ∃ n₀ : ℕ, ∀ G : SrcGraph, IsShape Δ G → IsNo γ G →
      n₀ < G.n →
      let L := Nat.clog 2 G.n
      let s := pow2 (2 ^ 16 * (L + 1))
      s ^ 4 ≤ 2 ^ L ∧ (∃ t : ℕ, q2 G s t = s ^ 2 * 2 ^ L) ∧
      ∀ (t : ℕ), q2 G s t = s ^ 2 * 2 ^ L → ∀ (ord : Item s G.n ↪ ℕ) (R : WMat),
        3 ≤ Dcost R.entry → DeletionBounds R.entry R.μX R.μY (1 / 2 ^ L) (Dcost R.entry) →
        (SrcData.full R G s t ord).TemplateDeletionBounds L ∧
        (SrcData.full R G s t ord).CollisionBound L ∧ Ineq10 Δ γ G s L ∧
        ExactlyIndepW (SrcData.full R G s t ord).TS.ν (SrcData.full R G s t ord).TS.z 8
          (jWt R s) ∧
        ExactlyIndepW (SrcData.full R G s t ord).TB.ν (SrcData.full R G s t ord).TB.z 8
          (j2Wt (SrcData.full R G s t ord).TΓ (q2 G s t))) ∧
    (∀ Δ : ℕ, 1 ≤ Δ → ∀ γ : ℚ, 0 < γ → ∃ s₀ : ℕ, (∃ e : ℕ, s₀ = 2 ^ e) ∧
      (∀ (G : SrcGraph) (s : ℕ), IsShape Δ G → (∃ e : ℕ, s = 2 ^ e) → s₀ ≤ s → G.n ≤ s ^ 4 →
        ∃ t : ℕ, q2 G s t = s ^ 6) ∧
      ∀ D : SrcData, IsShape Δ D.G → IsNo γ D.G → (∃ e : ℕ, D.s = 2 ^ e) → s₀ ≤ D.s →
        D.G.n ≤ D.s ^ 4 → D.q = D.s ^ 6 → D.TΩ = D.TΓ.tailList → D.ExplicitLists →
        3 ≤ Dcost D.R.entry →
        DeletionBounds D.R.entry D.R.μX D.R.μY (1 / 2 ^ (4 * Nat.log 2 D.s)) (Dcost D.R.entry) →
        D.TemplateDeletionBounds (4 * Nat.log 2 D.s) ∧ D.CollisionBound (4 * Nat.log 2 D.s) ∧
        Ineq10 Δ γ D.G D.s (4 * Nat.log 2 D.s) ∧
        ExactlyIndepW D.TS.ν D.TS.z 8 (jWt D.R D.s) ∧
        ExactlyIndepW D.TB.ν D.TB.z 8 (j2Wt D.TΓ D.q)) := by sorry

end DetCCHard.Supplement
