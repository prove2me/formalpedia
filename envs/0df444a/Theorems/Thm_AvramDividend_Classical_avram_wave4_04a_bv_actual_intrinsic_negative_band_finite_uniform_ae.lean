-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_bv_actual_intrinsic_negative_band_finite_uniform_ae
-- name    : AvramDividend.Classical.avram_wave4_04a_bv_actual_intrinsic_negative_band_finite_uniform_ae
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T11:52:29.046332+00:00
-- url     : https://prove2.me/theorems/97211fda-5c2c-432c-ba90-896446fbc60a
-- title:
--   One original-source BV probability-one event supports finite jump-measure mass for every negative band and horizon
-- statement:
--   There is one P-probability-one event for the actual original bounded-variation spectrally negative Lévy process X on which its intrinsic genuine pathwise jump measure N_X(ω) has finite mass on every separated negative mark rectangle (0,T]×(-∞,-ε], simultaneously for all finite T and every ε>0. The quantifiers on time and jump threshold lie inside the almost-sure event (strictly stronger than fixed-T, fixed-ε local finiteness), making it robust for random stopping horizons and subsequent predictable/localized constructions. It directly uses the already accepted finite-subset source Stieltjes jump budget, derives finite jump times by ε-weight cardinal contradiction, and evaluates the genuine N_X rectangle via the accepted actual path measure. It does not imply Poisson counts or predictable compensation.
-- source:
--   Canonical Proved source b02ad279-2e42-493a-ab8a-e763119bdffe (uniform all-T finite-subset jump budget), f6336d40-2d19-444f-bacd-83724316de67 (original path rectangle N_X mass), pinned ENNReal.exists_nat_mul_gt, Set.Infinite.exists_subset_card_eq and Set.Finite.exists_encard_eq_coe. No same-law substitution.

import Mathlib.Data.ENNReal.Inv
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Set.Card
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_actual_intrinsic_jump_measure_rectangle_encard
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_bv_actual_finite_source_jump_magnitudes_le_residual

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

theorem AvramDividend.Classical.avram_wave4_04a_bv_actual_intrinsic_negative_band_finite_uniform_ae
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation) :
    ∀ᵐ ω ∂P, ∀ (T : ℝ≥0) (ε : ℝ), 0 < ε →
      ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ Iic (-ε)) < ⊤ := by sorry
