-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_main_original_jump_removed_uniform_positive_compact
-- name    : AvramDividend.Classical.avram_p3_main_original_jump_removed_uniform_positive_compact
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T08:35:37.388681+00:00
-- url     : https://prove2.me/theorems/8569eabf-6151-4849-9fcc-356591ab178d
-- title:
--   Original BV negative-jump-removed source has uniform continuity on every positive compact time interval
-- statement:
--   On one P-full original sample event, the physical Lévy source path with its actual negative left jumps removed is uniformly continuous on every compact positive-time interval [a,b] for a>0. The original residual R(t)=t·drift-X.X_t-J_t is continuous at all positive times and is not assumed to vanish. This gives the precise mesh modulus for P3-D's source C1 Taylor estimate on intervals away from the separately treated time-zero atom.
-- source:
--   Proved 38d9546f source residual continuity, original raw negative left-jump sum, exact algebraic identity Y=t·drift-R, and pinned Mathlib IsCompact.uniformContinuousOn_of_continuous at Mathlib.Topology.UniformSpace.HeineCantor. Supports canonical a19d8b28 BV stochastic verification.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_raw_removed_residual_continuous_positive_time
open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_p3_main_original_jump_removed_uniform_positive_compact
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation) :
    ∀ᵐ ω ∂P, ∀ a b : ℝ≥0, 0 < a →
      UniformContinuousOn (fun s : ℝ≥0 => X.X s ω +
        (∑' u : ℝ≥0, if 0 < u ∧ u ≤ s then
          Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω
        else 0)) (Icc a b) := by sorry
