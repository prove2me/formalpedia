-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB51_original_barrier_upperstrip_physical_GH_coefficients
-- name    : AvramDividend.Classical.avram_gbB51_original_barrier_upperstrip_physical_GH_coefficients
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T16:24:22.225369+00:00
-- url     : https://prove2.me/theorems/eef3db83-f9d6-4409-bf34-745074e103bc
-- title:
--   Original finite-cap physical Gaussian mesh has G=discount and H=0 on the positive upper-strip tube
-- statement:
--   On the true original barrier reserve with x=C=1/8 and fixed finite-cap j=9 (upper threshold 5/44), narrow source fluctuations force the prepayment mesh reserve above the upper threshold. Because the original rightLimit D equals D, its original physical-grid first-order Gaussian coefficient is precisely exp(-qs) and its Hessian coefficient is zero at every grid time before T. This isolates the centred Gaussian physical-grid increment.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gbB38_barrier_reserve_above_cutoff_on_tube
import Theorems.Thm_AvramDividend_Classical_avram_gbB41_original_barrier_postpayment_rightLimit_eq
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_gbB51_original_barrier_upperstrip_physical_GH_coefficients
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T s : ℝ≥0)
    (ω : Ω) (hTube : ∀ u : ℝ≥0, u ≤ T →
      |X.X u ω| ≤ (1 / 400 : ℝ)) (hs : s < T)
    (q a : ℝ) (w : ℝ → ℝ) :
    let y : ℝ := (1 / 8 : ℝ) + X.X s ω -
      rightLimit (barrierStrategy X (1 / 8 : ℝ) (1 / 8 : ℝ)) s ω
    (Real.exp (-(q * (s : ℝ))) *
      (if y ∈ Icc a (5 / 44 : ℝ) then deriv w y else 1) =
        Real.exp (-(q * (s : ℝ)))) ∧
    ((1 / 2 : ℝ) * Real.exp (-(q * (s : ℝ))) *
      (if y ∈ Icc a (5 / 44 : ℝ) then iteratedDeriv 2 w y else 0) = 0)
    := by sorry
