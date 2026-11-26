-- Prove2me | Theorems.Thm_BranchActualQ_negative_seed_generates_stationary_minimum_sequence
-- name    : BranchActualQ.negative_seed_generates_stationary_minimum_sequence
-- status  : Proved
-- author  : @bueno_ricardo
-- created : 2026-11-18T09:02:57.957467+00:00
-- url     : https://prove2.me/theorems/81253a11-93e2-487f-92f4-a58d1e8a664b
-- title:
--   Original Q: one negative seed generates global stationary negative minima at every later order
-- statement:
--   Define $f(s)=(1+s(s-1)\Lambda_0(s))/2$, where $\Lambda_0$ is Mathlib's entire completed-zeta function, and $G(x)=\operatorname{Re}f(1/2+\sqrt{x})$. For the original sensor
--   $$Q_n(u)=2^n u^{2n-1}(-1)^{n-1}\frac{d^n}{dx^n}(\log G(x)-\log G(0))\bigg|_{x=u^2},$$
--   let $n_0\ge1$, $u_0>0$, and suppose $Q_{n_0}(u_0)<0$. There is a sequence $v_j>0$ such that, for every integer $j\ge0$, $v_j$ is a global minimizer of $Q_{n_0+j}$ on the positive axis, $Q_{n_0+j}(v_j)<0$, and its derivative exists and equals zero. Furthermore,
--   $$Q_{n_0}(v_0)\le Q_{n_0}(u_0),\qquad Q_{n_0+j+1}(v_{j+1})\le(2(n_0+j)-1)Q_{n_0+j}(v_j).$$
--   The final statement assumes only the negative seed at an admissible index and point. It neither asserts that such a seed exists nor excludes one.
-- source:
--   Desenvolvimento RH, On the Infinitude of Off-Critical Zeros, Section 2 negative-minimum cascade, concretely reconstructed 2026-11-18. Builds on BranchActualQ.negative_seed_has_interior_global_minimum, ACCEPTED submission 94d7021e-5713-4021-b70b-33ad3d664777. Inherited source attribution: Desenvolvimento RH, original Q regularity and compactness obligation, 2026-11-17. Uses the already proved paired xi product, concrete upper-zero lower bound, original-occurrence sublinear count and uniform small-scale positivity. Source attribution inherited from prior certificate: Desenvolvimento RH — Ricardo Marangoni Brandão Bueno. Exact bridge/composition for the original sensor, reusing XiPairingPublished.concrete_G_zero_product, XiQuantitativePublished.concrete_upper_zero_lower, BranchActualCount.original_occurrence_sublinear_bound, and BranchActualCount.original_occurrence_uniform_small_scale_positive. Analytic sources: PrimeNumberTheoremAnd commits a4fb6989b07e9c76b511807ae93e33e25b820e9b and 0a2c672d7533437e50f7a72596cb0ecd17352fbe; smmercuri/zeta commit 3dab6480a82f1bfc5de0a59550e279cf50490033; teal-sea/zeta-lab commit a401821c9608526425f3d4cf7ff8e59bc37e1c79. Original authors/copyright and Apache-2.0 materials retained. No mathematical novelty claim.

import Mathlib

theorem BranchActualQ.negative_seed_generates_stationary_minimum_sequence :
    let f : ℂ → ℂ := fun s => (1+s*(s-1)*completedRiemannZeta₀ s)/2
    let G : ℝ → ℝ := fun x => (f (1/2+(Real.sqrt x : ℂ))).re
    let Q : ℕ → ℝ → ℝ := fun n u =>
      (2 : ℝ)^n*u^(2*n-1)*(-1 : ℝ)^(n-1)*
        iteratedDeriv n (fun x => Real.log (G x)-Real.log (G 0)) (u^2)
    ∀ (n₀ : ℕ), 1 ≤ n₀ → ∀ u₀ > 0, Q n₀ u₀ < 0 →
    ∃ v : ℕ → ℝ,
      Q n₀ (v 0) ≤ Q n₀ u₀ ∧
      ∀ j : ℕ, 0 < v j ∧ Q (n₀+j) (v j) < 0 ∧
        (∀ u > 0, Q (n₀+j) (v j) ≤ Q (n₀+j) u) ∧
        IsLocalMin (Q (n₀+j)) (v j) ∧ HasDerivAt (Q (n₀+j)) 0 (v j) ∧
        Q (n₀+(j+1)) (v (j+1)) ≤ (2*((n₀+j : ℕ) : ℝ)-1)*Q (n₀+j) (v j) := by sorry
