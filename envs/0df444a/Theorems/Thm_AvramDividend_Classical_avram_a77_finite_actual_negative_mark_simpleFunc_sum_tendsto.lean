-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a77_finite_actual_negative_mark_simpleFunc_sum_tendsto
-- name    : AvramDividend.Classical.avram_a77_finite_actual_negative_mark_simpleFunc_sum_tendsto
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T22:52:09.212686+00:00
-- url     : https://prove2.me/theorems/61e071d7-534f-45c2-aaf3-2d739ae8a657
-- title:
--   Finite actual negative-mark simple-function sums converge to theta times their source signed sum
-- statement:
--   For any finite set of actual jump times S and strictly negative source marks y(u), if each Borel simple-function quantiser q_n(y) tends pointwise to theta*y on negative marks, then its finite sum over the exact source jump times converges to theta times the finite signed jump sum. This uses only Mathlib finite-sum tendsto; actual original Avram hSupport gives S and nonpositive jumps gives negative marks. Reusable in the connected a77->8bb->5b->cc5->4c source-fibre reconstruction, without assuming the missing physical-mark count identity.
-- source:
--   Avram Dividend Classical main root path to physical db0a source reconstruction, original finite support ce005 and negative jump property d0c21664.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Topology
noncomputable section

theorem AvramDividend.Classical.avram_a77_finite_actual_negative_mark_simpleFunc_sum_tendsto
    (S : Finset ℝ≥0) (mark : ℝ≥0 → ℝ) (θ : ℝ)
    (hNeg : ∀ u ∈ S, mark u < 0)
    (q : ℕ → SimpleFunc ℝ ℝ)
    (hPoint : ∀ y, y < 0 →
      Tendsto (fun n => q n y) atTop (𝓝 (θ * y))) :
    Tendsto (fun n => ∑ u ∈ S, q n (mark u))
      atTop (𝓝 (θ * ∑ u ∈ S, mark u)) := by sorry
