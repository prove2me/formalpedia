-- Prove2me | Theorems.Thm_BranchActualQ_negative_seed_has_interior_global_minimum
-- name    : BranchActualQ.negative_seed_has_interior_global_minimum
-- status  : Proved
-- author  : @bueno_ricardo
-- created : 2026-11-17T09:45:39.173169+00:00
-- url     : https://prove2.me/theorems/50fa6d77-7be3-49e7-81ca-88df48bf298f
-- title:
--   Original Q: a negative seed yields an interior global minimum with derivative zero
-- statement:
--   Let $f(s)=(1+s(s-1)\Lambda_0(s))/2$, where $\Lambda_0$ is Mathlib's entire completed-zeta function, and set $G(x)=\operatorname{Re} f(1/2+\sqrt x)$. For the original sensor
--   $$Q_n(u)=2^n u^{2n-1}(-1)^{n-1}\frac{d^n}{dx^n}\bigl(\log G(x)-\log G(0)\bigr)\bigg|_{x=u^2},$$
--   if $n\ge1$, $u_0>0$ and $Q_n(u_0)<0$, then there is $v>0$ with $Q_n(v)\le Q_n(u_0)$, $Q_n(v)\le Q_n(u)$ for every $u>0$, and $Q_n$ has a local minimum at $v$ and a derivative equal to zero there. The only assumptions in the final statement are the admissible index, positive seed location, and negative seed value. It does not assert the existence of a negative seed or exclude it, and does not prove the full Branches or RH.
-- source:
--   Desenvolvimento RH, original Q regularity and compactness obligation, 2026-11-17. Uses the already proved paired xi product, concrete upper-zero lower bound, original-occurrence sublinear count and uniform small-scale positivity. Source attribution inherited from prior certificate: Desenvolvimento RH — Ricardo Marangoni Brandão Bueno. Exact bridge/composition for the original sensor, reusing XiPairingPublished.concrete_G_zero_product, XiQuantitativePublished.concrete_upper_zero_lower, BranchActualCount.original_occurrence_sublinear_bound, and BranchActualCount.original_occurrence_uniform_small_scale_positive. Analytic sources: PrimeNumberTheoremAnd commits a4fb6989b07e9c76b511807ae93e33e25b820e9b and 0a2c672d7533437e50f7a72596cb0ecd17352fbe; smmercuri/zeta commit 3dab6480a82f1bfc5de0a59550e279cf50490033; teal-sea/zeta-lab commit a401821c9608526425f3d4cf7ff8e59bc37e1c79. Original authors/copyright and Apache-2.0 materials retained. No mathematical novelty claim.

import Mathlib

theorem BranchActualQ.negative_seed_has_interior_global_minimum :
    let f : ℂ → ℂ := fun s => (1+s*(s-1)*completedRiemannZeta₀ s)/2
    let G : ℝ → ℝ := fun x => (f (1/2+(Real.sqrt x : ℂ))).re
    let Q : ℕ → ℝ → ℝ := fun n u =>
      (2 : ℝ)^n*u^(2*n-1)*(-1 : ℝ)^(n-1)*
        iteratedDeriv n (fun x => Real.log (G x)-Real.log (G 0)) (u^2)
    ∀ (n : ℕ), 1 ≤ n → ∀ u₀ > 0, Q n u₀ < 0 →
      ∃ v > 0, Q n v ≤ Q n u₀ ∧ (∀ u > 0, Q n v ≤ Q n u) ∧
        IsLocalMin (Q n) v ∧ HasDerivAt (Q n) 0 v := by sorry
