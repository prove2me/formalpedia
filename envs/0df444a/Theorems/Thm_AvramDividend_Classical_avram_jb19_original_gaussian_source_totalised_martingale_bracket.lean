-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jb19_original_gaussian_source_totalised_martingale_bracket
-- name    : AvramDividend.Classical.avram_jb19_original_gaussian_source_totalised_martingale_bracket
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T13:12:24.076889+00:00
-- url     : https://prove2.me/theorems/f58474f2-2b2c-4fa8-a6be-7eb0ad761906
-- title:
--   Total original Gaussian source with exact Lévy mesh decomposition, martingale conditional means and variance
-- statement:
--   Construct a pathwise-total Gaussian source on the original sample space from the physical Levy path, compensated small marks and uncompensated large jumps. It agrees simultaneously at every time almost surely with the intrinsic Gaussian residual. Transfer its deterministic-time integrability, initial/right-continuous filtration conditional martingale identity and quadratic expectation exactly, giving a source-certified field for the finite-mesh Ito-Meyer argument.
-- source:
--   Proved ce29c6e1 physical source path equality and exact almost-everywhere congruence of integrability, conditional expectation and second moments. Required bridge to mixed original Ito ledger 544e8511 and compact-clock source budgeting.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_large_jump_sum
import Theorems.Thm_AvramDividend_Classical_avram_ja18t_original_J_physical_jump_decomposition
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_jb19_original_gaussian_source_totalised_martingale_bracket
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (R Jsmall : ℝ≥0 → Ω → ℝ)
    (hRsource : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto
        (fun k : ℕ =>
          avram_p4_h_gaussian_intrinsic_truncated_residual X k t ω)
        atTop (nhds (R t ω)))
    (hJsource : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto
        (fun k : ℕ =>
          avram_p4_h_gaussian_intrinsic_small_band_compensated X k t ω)
        atTop (nhds (Jsmall t ω)))
    (hRint : ∀ t : ℝ≥0, Integrable (R t) P)
    (hRmart : ∀ s t : ℝ≥0, s ≤ t →
      ∀ᵐ ω ∂P,
        condExp (𝓕.rightCont s) P (R t) ω = R s ω)
    (hRbracket : ∀ t : ℝ≥0,
      Integrable (fun ω => (R t ω) ^ 2) P ∧
      (∫ ω, (R t ω) ^ 2 ∂P) = (t : ℝ) * X.σ ^ 2) :
    ∃ M : ℝ≥0 → Ω → ℝ,
      (∀ t ω, X.X t ω =
        (t : ℝ) * X.c + M t ω + Jsmall t ω +
          avram_p4_h_gaussian_intrinsic_large_jump_sum X t ω) ∧
      (∀ᵐ ω ∂P, ∀ t : ℝ≥0, M t ω = R t ω) ∧
      (∀ t : ℝ≥0, Integrable (M t) P) ∧
      (∀ s t : ℝ≥0, s ≤ t →
        ∀ᵐ ω ∂P,
          condExp (𝓕.rightCont s) P (M t) ω = M s ω) ∧
      (∀ t : ℝ≥0,
        Integrable (fun ω => (M t ω) ^ 2) P ∧
        (∫ ω, (M t ω) ^ 2 ∂P) = (t : ℝ) * X.σ ^ 2) := by sorry
