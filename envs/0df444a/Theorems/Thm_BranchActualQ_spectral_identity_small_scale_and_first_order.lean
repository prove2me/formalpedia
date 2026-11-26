-- Prove2me | Theorems.Thm_BranchActualQ_spectral_identity_small_scale_and_first_order
-- name    : BranchActualQ.spectral_identity_small_scale_and_first_order
-- status  : Proved
-- author  : @bueno_ricardo
-- created : 2026-11-17T08:36:46.24043+00:00
-- url     : https://prove2.me/theorems/60b617c4-80d1-4d47-b117-22fec9062dfd
-- title:
--   Original Q: exact spectral identity, uniform small-scale positivity and first-order nonnegativity
-- statement:
--   For the original xi-based G and original differential sensor Q_n(u), with original upper zero occurrences and analytic multiplicities, Q_n(u) equals 2^n (n-1)!/u times the real part of the normalized spectral power sum, for every n>=1 and u>0. There exists a single delta>0 such that Q_n(u)>0 for all n>=2, u>0 with sqrt(n)/u<delta. Also Q_1(u)>=0 for every u>0. No RH, unproved low-zero certification, counting or positivity hypotheses occur in the final statement.
-- source:
--   Desenvolvimento RH — Ricardo Marangoni Brandão Bueno. Exact bridge/composition for the original sensor, reusing XiPairingPublished.concrete_G_zero_product, XiQuantitativePublished.concrete_upper_zero_lower, BranchActualCount.original_occurrence_sublinear_bound, and BranchActualCount.original_occurrence_uniform_small_scale_positive. Analytic sources: PrimeNumberTheoremAnd commits a4fb6989b07e9c76b511807ae93e33e25b820e9b and 0a2c672d7533437e50f7a72596cb0ecd17352fbe; smmercuri/zeta commit 3dab6480a82f1bfc5de0a59550e279cf50490033; teal-sea/zeta-lab commit a401821c9608526425f3d4cf7ff8e59bc37e1c79. Original authors/copyright and Apache-2.0 materials retained. No mathematical novelty claim.

import Mathlib

theorem BranchActualQ.spectral_identity_small_scale_and_first_order :
    let f : ℂ → ℂ := fun s => (1+s*(s-1)*completedRiemannZeta₀ s)/2
    let I := (s : {s : ℂ // f s = 0 ∧ 0 < s.im}) × Fin (analyticOrderNatAt f s.val)
    let G : ℝ → ℝ := fun x => (f (1/2+(Real.sqrt x : ℂ))).re
    let Q : ℕ → ℝ → ℝ := fun n u =>
      (2 : ℝ)^n*u^(2*n-1)*(-1 : ℝ)^(n-1)*
        iteratedDeriv n (fun x => Real.log (G x)-Real.log (G 0)) (u^2)
    (∀ n ≥ 1, ∀ u > 0,
      Q n u = (2 : ℝ)^n*((n-1).factorial : ℝ)/u *
        (∑' i : I, (((u^2 : ℝ) : ℂ)/((u^2 : ℂ)-(i.1.val-1/2)^2))^n).re) ∧
    (∃ δ > (0 : ℝ), ∀ (n : ℕ), 2 ≤ n → ∀ u > 0,
      Real.sqrt (n : ℝ)/u < δ → 0 < Q n u) ∧
    (∀ u > 0, 0 ≤ Q 1 u) := by sorry
