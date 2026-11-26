-- Prove2me | Theorems.Thm_BranchActualCount_original_occurrence_uniform_small_scale_positive
-- name    : BranchActualCount.original_occurrence_uniform_small_scale_positive
-- status  : Proved
-- author  : @bueno_ricardo
-- created : 2026-11-17T07:51:57.682195+00:00
-- url     : https://prove2.me/theorems/f7f7bb26-7b58-4ce6-a93f-0f0decd98a7a
-- title:
--   Uniform small-scale positivity for the original xi zero occurrences
-- statement:
--   Let xi(s)=(1+s(s−1) completedRiemannZeta₀(s))/2, and index all its upper-half-plane zeros with analytic multiplicity by I. Write γᵢ=Im(ρᵢ), εᵢ=Re(ρᵢ)−1/2. There exists δ>0 such that for every real h with 0<h<δ and every integer k≥2, with x=k/h², the series ∑ᵢ (x/(x+γᵢ²−εᵢ²−2i εᵢγᵢ))^k is summable and has strictly positive real part. δ is independent of k. No explicit numerical value of δ is claimed. All zero-counting hypotheses are discharged for the original xi occurrences; RH, simplicity of zeros, low-zero verification and positivity of the original Q are not premises. This theorem covers the spectral small-scale regime only, not the complete Branches or the whole domain of the original Q.
-- source:
--   Desenvolvimento RH — Ricardo Marangoni Brandão Bueno. Concrete instantiation of the accepted two-cutoff theorem BranchComposition.small_scale_positive_from_counts, followed by an elementary sequential-to-uniform argument. Counting inputs derive from the analytic formalization of Salvatore Mercuri and Bhavik Mehta, smmercuri/zeta commit 3dab6480a82f1bfc5de0a59550e279cf50490033 and PrimeNumberTheoremAnd commit 0a2c672d7533437e50f7a72596cb0ecd17352fbe. Copyright headers and Apache-2.0 attribution preserved in the expanded reproducibility source. No claim of mathematical novelty.

import Mathlib

theorem BranchActualCount.original_occurrence_uniform_small_scale_positive :
    let xi : ℂ → ℂ := fun s => (1+s*(s-1)*completedRiemannZeta₀ s)/2
    let I := (s : {s : ℂ // xi s = 0 ∧ 0 < s.im}) × Fin (analyticOrderNatAt xi s.val)
    let S : ℕ → ℝ → I → ℂ := fun k h i =>
      (((((k : ℝ)/h^2 : ℝ) : ℂ) /
        ((((k : ℝ)/h^2+i.1.val.im^2-(i.1.val.re-1/2)^2 : ℝ) : ℂ) -
          (2*(i.1.val.re-1/2)*i.1.val.im : ℝ)*Complex.I)) ^ k)
    ∃ δ > (0 : ℝ), ∀ h, 0 < h → h < δ → ∀ k ≥ 2,
      Summable (S k h) ∧ 0 < (∑' i, S k h i).re := by
  sorry
