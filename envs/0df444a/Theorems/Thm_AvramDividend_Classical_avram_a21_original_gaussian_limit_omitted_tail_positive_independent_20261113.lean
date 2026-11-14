-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a21_original_gaussian_limit_omitted_tail_positive_independent_20261113
-- name    : AvramDividend.Classical.avram_a21_original_gaussian_limit_omitted_tail_positive_independent_20261113
-- status  : Open
-- author  : @WillR
-- created : 2026-11-13T10:21:47.826096+00:00
-- url     : https://prove2.me/theorems/d21f93fd-bdad-4ce7-b969-503ad0f7c6f6
-- title:
--   Strictly positive-horizon original Gaussian-limit independent of genuinely omitted compensated negative marks
-- statement:
--   On the ACTUAL original Lévy sample space, the physical Gaussian residual limit R at each positive horizon is independent of the genuinely OMITTED near-zero compensated negative jump tail Rn-R. This follows from same-source Lévy-Itô Gaussian-versus-Poisson noise disjointness or joint-characteristic-function factorisation, never from the false R0 versus RETAINED mark-band independence. Once this core is Proved, the remaining product covariance follows from separately proved physical Gaussian centring and tail L1.
-- source:
--   True Gaussian-versus-Poisson source independence and original physical cutoff identity cb474bae, Gaussian source limit identity 2affdece.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_a21_original_gaussian_limit_omitted_tail_positive_independent_20261113
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (R : ℝ≥0 → Ω → ℝ)
    (hR : ∀ᵐ ω ∂P, ∀ T : ℝ≥0,
      Tendsto (fun k : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X k T ω)
        atTop (nhds (R T ω))) :
    ∀ (n : ℕ) (t : ℝ≥0), 0 < t →
      ProbabilityTheory.IndepFun
        (R t)
        (fun ω => avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω - R t ω)
        P := by sorry
