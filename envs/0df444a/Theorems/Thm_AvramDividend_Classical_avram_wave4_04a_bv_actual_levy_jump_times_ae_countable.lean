-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_bv_actual_levy_jump_times_ae_countable
-- name    : AvramDividend.Classical.avram_wave4_04a_bv_actual_levy_jump_times_ae_countable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T09:44:17.613735+00:00
-- url     : https://prove2.me/theorems/02fe4413-e8d4-47c4-97c7-73ea3d16cd74
-- title:
--   Actual bounded-variation Lévy jump-time support is countable on one probability-one event
-- statement:
--   For the genuine original bounded-variation spectrally negative Lévy process X, a P-probability-one set of paths has countably many positive-time nonzero jump marks ΔX_t=X_t−X_{t−}. This follows from the already canonically Proved global monotonicity of the original drift residual Y_t=t·X.drift−X_t and the Mathlib countable-discontinuities theorem for monotone functions. A jump of X at a positive time forces a discontinuity of Y because the linear drift is continuous. The conclusion refers to the original X sample paths and requires no Poisson-space extension.
-- source:
--   Avram–Palmowski–Pistorius (2007) BV finite-variation Lévy path. Original residual monotone a.s. Proved f6cc1059-e8ca-403e-8d73-71a139d3dc4c; pinned Mathlib Monotone.countable_not_continuousAt, leftLim_eq_of_tendsto.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_bv_actual_levy_residual_ae_monotone_all_times

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_04a_bv_actual_levy_jump_times_ae_countable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation) :
    ∀ᵐ ω ∂P,
      Set.Countable {t : ℝ≥0 |
        0 < t ∧ X.X t ω ≠ Function.leftLim
          (fun s : ℝ≥0 => X.X s ω) t} := by sorry
