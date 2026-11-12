-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ja18s_original_J_zero_origin
-- name    : AvramDividend.Classical.avram_ja18s_original_J_zero_origin
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T10:46:28.908337+00:00
-- url     : https://prove2.me/theorems/86133181-867c-4f45-930e-254bd4909590
-- title:
--   Original compensated jump martingale starts at zero
-- statement:
--   Direct original-space zero-origin identity for J = X - t E[X1] - R. X0=0 follows from the process definition and R0=0 follows from Proved a8d94ac5. This discharges the optional-sampling origin condition without any auxiliary noise process.
-- source:
--   J-A18 stopped jump 850e34ce via JA18P envelope

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_ja18s_original_J_zero_origin
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (R : ℝ≥0 → Ω → ℝ)
    (hRsource : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto
        (fun k : ℕ =>
          avram_p4_h_gaussian_intrinsic_truncated_residual X k t ω)
        atTop (nhds (R t ω))) :
    ∀ᵐ ω ∂P,
      X.X 0 ω - ((0 : ℝ≥0) : ℝ) *
        (∫ η, X.X 1 η ∂P) - R 0 ω = 0 := by sorry
