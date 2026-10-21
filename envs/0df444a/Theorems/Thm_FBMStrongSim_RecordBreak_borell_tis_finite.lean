-- Prove2me | Theorems.Thm_FBMStrongSim_RecordBreak_borell_tis_finite
-- name    : FBMStrongSim.RecordBreak.borell_tis_finite
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:00:53.941128+00:00
-- url     : https://prove2.me/theorems/0d08a1fb-b49f-499b-b6cb-daf772ad5b5e
-- title:
--   Borell–TIS inequality (cited at (3.6), p. 9) — P(max|X_i| − E max|X_i| > u) ≤ exp(−u²/2σ²)
-- statement:
--   Let $(X_1,\dots,X_n)$, $n\ge1$, be a centered Gaussian random vector (jointly Gaussian, not necessarily independent) with $\operatorname{Var}(X_i)\le\sigma^2$ for every $i$, where $\sigma>0$. Then for every $u>0$,
--   $$\mathbb P\Big(\max_{1\le i\le n}|X_i|-\mathbb E\Big[\max_{1\le i\le n}|X_i|\Big]>u\Big)\le\exp\Big\{-\frac{u^2}{2\sigma^2}\Big\}.$$
--
--   This is the Borell–TIS inequality in the finite form in which the paper invokes it, at (3.6) for the variance part $\max_j|a^k_j-c^k_j|$ under $\mathbb P_{k-1}$ and again on p. 11 for the bias part $\max_j|c^k_j-b^k_j|$. The paper cites it without stating it.
--
--   **Formalization Note** Joint Gaussianity is `HasGaussianLaw` of the vector $(X_1,\dots,X_n)$. The maximum is over the finite nonempty index set, so it is the true maximum.
-- source:
--   Chen, Dong & Ni, ε-Strong simulation of fractional Brownian motion and related stochastic differential equations, arXiv:1902.07824v1, p. 9, (3.6) and p. 11 (Borell–TIS inequality, cited)

import Mathlib

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace FBMStrongSim.RecordBreak

/-- The Borell–TIS inequality for finitely many Gaussians, as cited at (3.6), p. 9 and in step (B),
p. 11: if `(X_1, …, X_n)` (`n ≥ 1`) is a centered Gaussian vector whose coordinates have variance at
most `σ²`, then for `u > 0`,
`P(max_i |X_i| − E[max_i |X_i|] > u) ≤ exp{−u² / (2σ²)}`. -/
theorem borell_tis_finite {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {n : ℕ} (hn : 0 < n) (X : Fin n → Ω → ℝ)
    (hX : HasGaussianLaw (fun ω i => X i ω) P) (hcent : ∀ i, P[X i] = 0)
    {σ : ℝ} (hσ : 0 < σ) (hvar : ∀ i, Var[X i; P] ≤ σ ^ 2) {u : ℝ} (hu : 0 < u) :
    P {ω | (Finset.univ.sup' (Finset.univ_nonempty_iff.mpr ⟨⟨0, hn⟩⟩) fun i => |X i ω|)
        - P[fun ω' => Finset.univ.sup' (Finset.univ_nonempty_iff.mpr ⟨⟨0, hn⟩⟩)
            fun i => |X i ω'|] > u}
      ≤ ENNReal.ofReal (Real.exp (-u ^ 2 / (2 * σ ^ 2))) := by sorry

end FBMStrongSim.RecordBreak
