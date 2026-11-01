-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_bv_actual_truncated_negative_jump_times_finite_ae
-- name    : AvramDividend.Classical.avram_wave4_04a_bv_actual_truncated_negative_jump_times_finite_ae
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T11:28:33.537631+00:00
-- url     : https://prove2.me/theorems/69d28cd1-ae1f-4bee-a05d-eccb3bbd314f
-- title:
--   Actual bounded-variation Lévy has finitely many jumps above any positive size on each finite horizon
-- statement:
--   For the actual spectrally negative source Lévy process with bounded variation, and any horizon T and positive jump magnitude threshold ε, the set of true positive-time downward source jumps in (0,T] whose magnitude is at least ε is finite almost surely. The uniform pathwise finite-subset jump-budget theorem bounds every finite collection of such jumps by the finite residual T*d-X_T. If the set were infinite, pinned Set.Infinite.exists_subset_card_eq supplies arbitrary-cardinality finite subsets; ENNReal.exists_nat_mul_gt supplies a cardinal size whose ε-weight already exceeds the residual, a contradiction. This is actual-path locally finite truncated-band counting support, not yet random-measure measurability or a Poisson/compensator law.
-- source:
--   Canonical Proved BV genuine source jump finite-subset budget b02ad279-2e42-493a-ab8a-e763119bdffe; pinned Mathlib Set.Infinite.exists_subset_card_eq, ENNReal.exists_nat_mul_gt, ENNReal.ofReal_mono, Finset.sum_le_sum. Does not replace the original X.

import Mathlib.Data.ENNReal.Inv
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_bv_actual_finite_source_jump_magnitudes_le_residual

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

theorem AvramDividend.Classical.avram_wave4_04a_bv_actual_truncated_negative_jump_times_finite_ae
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (T : ℝ≥0) (ε : ℝ) (hε : 0 < ε) :
    ∀ᵐ ω ∂P,
      Set.Finite {u : ℝ≥0 | 0 < u ∧ u ≤ T ∧
        ε ≤ Function.leftLim (fun v : ℝ≥0 => X.X v ω) u - X.X u ω} := by sorry
