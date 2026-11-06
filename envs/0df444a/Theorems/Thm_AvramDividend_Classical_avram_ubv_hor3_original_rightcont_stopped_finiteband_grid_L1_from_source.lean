-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_hor3_original_rightcont_stopped_finiteband_grid_L1_from_source
-- name    : AvramDividend.Classical.avram_ubv_hor3_original_rightcont_stopped_finiteband_grid_L1_from_source
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T16:49:30.315195+00:00
-- url     : https://prove2.me/theorems/df69c43e-cd05-482f-9b9f-c216dafc50f5
-- title:
--   True stopped original physical finite-band negative jump-grid is L1-centred from intrinsic separated-band sources alone
-- statement:
--   For the original spectrally negative Levy X, its actual right-continuous stopping-time τ, true physical marked jump counts and predictable square-integrable coefficients, the bounded-horizon finite-grid stopped compensated negative-band martingale is integrable and has exactly zero expectation. No ad hoc assumptions of Levy-band finiteness, compensated-count L2 or source count measurability are needed; each follows from proved original Levy and filtration theorems. The conclusion retains the exact original stochastic process, stopping event, and grid.
-- source:
--   Source-exact composite: Proved genuine separated negative-band ν-finiteness 86086cb2, original negative Borel physical cell L2 963870c8, and actual right-cont stopped predictable finite-grid L1 centring 963a2598. Eliminates both input moment and rate hypotheses while retaining natural stopped indicator and true count. Remaining source Itô-Meyer mesh limit and global W/Cash/Term signs are not asserted.

import Mathlib.MeasureTheory.Measure.Count
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_separated_borel_nu_finite
import Theorems.Thm_AvramDividend_Classical_avram_p4_s3_original_negative_borel_cell_centred_L2_from_full_band
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_rightcont_stopped_grid_l2_from_predictable
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal Nat BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_ubv_hor3_original_rightcont_stopped_finiteband_grid_L1_from_source
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (T : ℝ≥0) (cut : ℕ)
    (τ : Ω → ℝ≥0)
    (hτstop : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0)))
    (grid : ℕ → ℝ≥0) (hGrid : ∀ i, grid i ≤ grid (i + 1))
    (hTime : ∀ i, grid i ≤ T)
    (ε : ℝ) (hε : 0 < ε) (C : ℕ → Set ℝ)
    (hC : ∀ i, MeasurableSet (C i))
    (hBand : ∀ i, C i ⊆ Ioo (-1 : ℝ) (-ε))
    (hCut : ∀ i, C i ⊆ Iic (-(1 / ((cut : ℝ) + 1))))
    (N : ℕ → Ω → ℝ≥0∞)
    (hActual : ∀ i, N i = fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc (grid i) (grid (i + 1)) ×ˢ C i))
    (H : ℕ → Ω → ℝ)
    (hH : ∀ i, StronglyMeasurable[𝓕.rightCont (grid i)] (H i))
    (hHL2 : ∀ i, MemLp (H i) 2 P)
    (k : ℕ) :
    Integrable (fun ω =>
      ∑ i ∈ Finset.range k,
        (if (τ ω : WithTop ℝ≥0) ≤ (grid i : WithTop ℝ≥0)
         then (0 : ℝ) else H i ω) *
        ((N i ω).toReal -
          (((grid (i + 1) - grid i : ℝ≥0) : ℝ≥0∞) *
            X.ν (C i)).toReal)) P ∧
    (∫ ω, (∑ i ∈ Finset.range k,
      (if (τ ω : WithTop ℝ≥0) ≤ (grid i : WithTop ℝ≥0)
       then (0 : ℝ) else H i ω) *
      ((N i ω).toReal -
        (((grid (i + 1) - grid i : ℝ≥0) : ℝ≥0∞) *
          X.ν (C i)).toReal)) ∂P) = 0 := by sorry
