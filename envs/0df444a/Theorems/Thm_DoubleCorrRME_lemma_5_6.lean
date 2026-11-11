-- Prove2me | Theorems.Thm_DoubleCorrRME_lemma_5_6
-- name    : DoubleCorrRME.lemma_5_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T09:57:18.796197+00:00
-- url     : https://prove2.me/theorems/ff7ee630-29b2-405f-bf7d-3e868d864a54
-- title:
--   Lemma 5.6, p.34 — sample-level QUE score dominance: $\sum_{\mathcal S_g}p\tau\le\sigma/32$
-- statement:
--   Work in the context of the sample-level filter: clean data $z$, observed data $x$ that are an $(\varepsilon,\alpha)$-double corruption with bad users $B$, the first stable reference $\mathcal I$ of Lemma 4.1, the §4.1 parameters $\alpha',\Delta,\kappa$, and $\varepsilon>10K_1\alpha'$ (Remark 5.4). Let $\mathcal R$ be the regular good users and $D_i$ the disagreement sets (Definition 5.2).
--
--   Let $u\in\{0,1/N\}^N$, $0\le w_{i,j}\le1/n$, $p=\mathrm{diag}(u)w$, $\Psi$ a density matrix and $\tau$ the QUE scores of Definition 3.8. Set
--
--   $$\mathcal S_g=\{(i,j):i\in\mathcal R,\ u_i>0,\ j\notin D_i\},\qquad \sigma=\langle\Psi,M_s(u,w)\rangle .$$
--
--   Suppose $\|\mathrm{vec}(p)\|_1\ge1-C_1\varepsilon$. For $\varepsilon$ sufficiently small and $C_Q$ a sufficiently large universal constant, if $\sigma\ge C_Q\kappa$ then
--
--   $$\sum_{(i,j)\in\mathcal S_g}p_{i,j}\tau_{i,j}\le\frac\sigma{32}.$$
--
--   So when the weighted covariance is large, most of the QUE score comes from samples outside the matched regular-good set, which is what lets the filter remove bad weight faster than good weight.
--
--   **Formalization Note** $C_1$ is quantified before $C_Q$ and the smallness of $\varepsilon$, which may depend on it.
--
--   Differences from the source:
--   - generalization: the universal constants C_ref, C_∆ of §4.1 (and K₀, K₁, C_Q) fixed once → ∀ C_ref, C_∆ > 0, then ∃ thresholds for K₀, K₁, C_Q; later constants may depend on earlier ones; reason: the statement holds for every choice of the §4.1 constants, so it specializes to the paper's fixed choice; every constant is still independent of N, n, d, ε, α, δ and the data
--   - reading: ∆ := O(√α′) (§4.1) and ∆ ← C_∆(√(d/m) + √α′ + √(L/m)) (Algorithm 2, line 2) → ∆ = C_∆√α′, κ = 1 + ∆²/α′; reason: §4.1 is the notation of §§4–5; since d/m, L/m ≤ α′/C_ref the two forms agree up to a change of C_∆, which is universally quantified
--   - reading: the lemma lives on the event of Lemma 4.1 for the corrupted data of Definition 1.1, under Remark 5.4's "we assume ε > 10K₁α′ throughout" and §4.1's δ ∈ (0, 0.1) → explicit hypotheses IsContext (|B| ≤ εN, at most αNn changed points outside B, |ℐ| ≥ (1 − α′)Nn, (α′, ∆)-stability of {z_k : k ∈ ℐ} w.r.t. (µ, I_d), δ ∈ (0, 1/10)) and 10K₁α′ < ε; reason: these are the standing assumptions of §5.2; the lemma is deterministic given them
--   - encoding: N users, n samples per user in ℝ^d → 1 ≤ N, 1 ≤ n, 1 ≤ d; reason: excludes only the empty settings, where the averages divide by 0
--   - generalization: Ψ^(t) the MMW density of Definition 3.7 → Ψ any density matrix (Ψ ⪰ 0, tr Ψ = 1); reason: every MMW density is a density matrix (Definition 3.7); the proof uses only these two properties
--   - encoding: ∥vec(p^(t))∥₁ ≥ 1 − O(ε), "for sufficiently small ε and sufficiently large C_Q" → ∀ C₁ > 0, ∃ C_Q⁰, ∀ C_Q ≥ C_Q⁰, ∃ c > 0, ε < c, ∥vec(p)∥₁ ≥ 1 − C₁ε; reason: Lemma 5.14 fixes C₁ first and then applies this lemma (proof of Lemma 5.14, p.41)
--   - encoding: u^(t) ∈ ℝ^N_{≥0}, w^(t) ∈ ℝ^{N×n}_{≥0} (Definition 3.8) → 0 ≤ w_{i,j} ≤ 1/n and u_i ∈ {0, 1/N}; reason: the nonnegativity of Definition 3.8 written out
-- source:
--   Aliakbarpour, Liu, Yin, Robust Mean Estimation Under Strong Double Corruption: Near-Linear Time and Sub-Gaussian Rate, STOC 2027 submission (manuscript sha256 49e26e5e…), Lemma 5.6, p.34 (PDF p.35); Definitions 5.2, 5.3, Remark 5.4, p.33

import Mathlib
import Definitions.Def_HighDimProb_QuadraticForms_OperatorNorm
import Definitions.Def_DoubleCorrRME_Model
import Definitions.Def_DoubleCorrRME_Stability
import Definitions.Def_DoubleCorrRME_Params
import Definitions.Def_DoubleCorrRME_Weights
import Definitions.Def_DoubleCorrRME_Filter

namespace DoubleCorrRME

/-- **Lemma 5.6** (sample-level QUE score dominance), p.34 (PDF p.35).

Aliakbarpour, Liu, Yin, *Robust Mean Estimation Under Strong Double Corruption: Near-Linear Time
and Sub-Gaussian Rate*, STOC 2027 submission (manuscript sha256 49e26e5e…).

"Let t ∈ ℤ_{≥0}, and let u^(t), w^(t), p^(t), Ψ^(t), τ^(t) be defined as in Definition 3.8. Suppose that
u^(t)_i ∈ {0, 1/N} and w^(t)_{i,j} ≤ 1/n for every i ∈ [N] and j ∈ [n]. We define
𝒮^(t)_g := {(i, j) ∈ [N] × [n] : i ∈ ℛ, u^(t)_i > 0, j ∉ D_i}. Suppose that ∥vec(p^(t))∥₁ ≥ 1 − O(ε).
For sufficiently small ε and a sufficiently large universal constant C_Q > 0, if
σ^(t) := ⟨Ψ^(t), M_s(u^(t), w^(t))⟩ ≥ C_Qκ, then ∑_{(i,j)∈𝒮^(t)_g} p^(t)_{i,j} τ^(t)_{i,j} ≤ σ^(t)/32."

**Formalization Note.**
* **Constants.** For every choice of the §4.1 constants `C_ref, C_∆ > 0` (Lemma 4.1 fixes one),
  `K₀` is a sufficiently large universal constant (Definition 5.2), `K₁ ≥ 2K₀` a sufficiently large
  one (Definition 5.3), `C_Q` a sufficiently large one (Lemma 5.6), and "for sufficiently small ε" is
  `ε < c`; every `O(·)` is one constant `C`. Each later constant may depend on the earlier ones and
  on nothing else (not on `N, n, d, ε, α, δ` or the data).
* **Context** (`IsContext`, see `Def_DoubleCorrRME_Filter`): one realization `(z, x, B, ℐ, µ)` with
  the corruption guarantee of Definition 1.1, `|ℐ| ≥ (1 − α′)Nn`, the `(α′, ∆)`-stability of
  `{z_k : k ∈ ℐ}` with respect to `(µ, I_d)` (Lemma 4.1, Part 1), `δ ∈ (0, 0.1)`, and the standing
  assumption `ε > 10K₁α′` of Remark 5.4 ("we assume ε > 10K₁α′ throughout the following analysis").
  `α′, ∆, κ` are those of §4.1 (`alphaP`, `deltaP`, `kappaP`); `𝒢, D_i, ℛ, θ₀, θ₁` are defined from
  the context. `N, n, d ≥ 1`.
* The constant `C₁` of "`∥vec(p^(t))∥₁ ≥ 1 − O(ε)`" is quantified universally before `C_Q` and the
  smallness of `ε`, which may depend on it: Lemma 5.14 fixes `C₁` first and then applies this
  lemma.
* The weights are nonnegative (`u ∈ ℝ^N_{≥0}`, `w ∈ ℝ^{N×n}_{≥0}`, Definition 3.8).
* `Ψ` is any density matrix (`Ψ ⪰ 0`, `tr Ψ = 1`), not only an MMW density; the proof uses only
  these two properties. `τ` is the exact QUE score `queScore` for `Ψ`. -/
theorem lemma_5_6 :
    ∀ Cref CΔ : ℝ, 0 < Cref → 0 < CΔ →
    ∃ K0min : ℝ, 0 < K0min ∧ ∀ K0 : ℝ, K0min ≤ K0 → ∀ K1 : ℝ, 2 * K0 ≤ K1 →
    ∀ C1 : ℝ, 0 < C1 →
    ∃ CQmin : ℝ, ∀ CQ : ℝ, CQmin ≤ CQ → ∃ c : ℝ, 0 < c ∧
    ∀ (N n d : ℕ), 1 ≤ N → 1 ≤ n → 1 ≤ d →
    ∀ (ε α δ : ℝ) (z x : Fin N → Fin n → Vec d) (B : Finset (Fin N))
      (I : Finset (Fin N × Fin n)) (μ : Vec d),
      IsContext Cref CΔ ε α δ z x B I μ → ε < c →
      let α' := alphaP Cref N n d α δ
      let κ := kappaP α' (deltaP CΔ α')
      10 * K1 * α' < ε →
      ∀ (u : Fin N → ℝ) (w : Fin N → Fin n → ℝ) (Ψ : Matrix (Fin d) (Fin d) ℝ),
        (∀ i, u i = 0 ∨ u i = 1 / (N : ℝ)) → (∀ i j, 0 ≤ w i j ∧ w i j ≤ 1 / (n : ℝ)) →
        IsDensity Ψ →
        1 - C1 * ε ≤ l1P (prodW u w) →
        CQ * κ ≤ frobInner Ψ (covS x u w) →
        ∑ k ∈ goodSet (regular K0 α' ε z x B I μ) (Dset z x I μ) u,
            prodW u w k.1 k.2 * queScore x u w Ψ k.1 k.2 ≤
          frobInner Ψ (covS x u w) / 32 := by sorry

end DoubleCorrRME
