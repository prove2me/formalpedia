-- Prove2me | Theorems.Thm_FBMStrongSim_RecordBreak_lemma_3_3
-- name    : FBMStrongSim.RecordBreak.lemma_3_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:00:56.471177+00:00
-- url     : https://prove2.me/theorems/e7900903-45b6-4b73-97e4-133679a0b94e
-- title:
--   Lemma 3.3, p. 10 — E[max_{i≤n}|X_i|] ≤ 2√(2 log(2n))·σ for centered Gaussians with variances ≤ σ²
-- statement:
--   Let $X_1,\dots,X_n$, $n\ge1$, be (not necessarily independent) centered Gaussian random variables whose variances are uniformly bounded by $\sigma^2$, $\sigma\ge0$. Then
--   $$\mathbb E\Big[\max_{1\le i\le n}|X_i|\Big]\le 2\sqrt{2\log(2n)}\cdot\sigma ,$$
--   with $\log$ the natural logarithm.
--
--   Combined with Lemma 3.2 this gives the bound $\mathbb E_{k-1}[\max_j|a^k_j-c^k_j|]\le 4\sqrt k\,2^{-kH}$ of (3.7), which removes the expectation from the Borell–TIS bound.
--
--   **Formalization Note** Only each $X_i$ is assumed Gaussian (no joint law), as in the lemma. The constant $2$ is the printed one.
-- source:
--   Chen, Dong & Ni, ε-Strong simulation of fractional Brownian motion and related stochastic differential equations, arXiv:1902.07824v1, p. 10, Lemma 3.3 (proof: Appendix A.2, p. 39)

import Mathlib

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace FBMStrongSim.RecordBreak

/-- Lemma 3.3, p. 10: if `X_1, …, X_n` (`n ≥ 1`, not necessarily independent) are centered
Gaussian random variables with variances at most `σ²`, then
`E[max_{1 ≤ i ≤ n} |X_i|] ≤ 2 √(2 log(2n)) · σ` (natural logarithm). -/
theorem lemma_3_3 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {n : ℕ} (hn : 0 < n) (X : Fin n → Ω → ℝ) (hX : ∀ i, HasGaussianLaw (X i) P)
    (hcent : ∀ i, P[X i] = 0) {σ : ℝ} (hσ : 0 ≤ σ) (hvar : ∀ i, Var[X i; P] ≤ σ ^ 2) :
    P[fun ω => Finset.univ.sup' (Finset.univ_nonempty_iff.mpr ⟨⟨0, hn⟩⟩) fun i => |X i ω|]
      ≤ 2 * Real.sqrt (2 * Real.log (2 * n)) * σ := by sorry

end FBMStrongSim.RecordBreak
