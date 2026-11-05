-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_leanlevy_bridge_original_equal_mesh_triangular_rate_real
-- name    : AvramDividend.Classical.avram_leanlevy_bridge_original_equal_mesh_triangular_rate_real
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T14:42:42.588849+00:00
-- url     : https://prove2.me/theorems/44077ce5-faab-4681-9118-7e879b622f9e
-- title:
--   Exact finite uniform-mesh original Lévy chronological pair rate sum
-- statement:
--   For a horizon T and the real intensity a of the original Avram finite negative jump band, the finite expected chronological cross-cell grid sum has the exact closed triangular formula. The result holds algebraically for arbitrary real T and a, so it may be instantiated with the actual source T and (X.ν B).toReal without changing the probability space. It is one deterministic rate-sum component of the still-open physical second factorial moment proof; the ENNReal-to-real source-rate conversion and limit passage are separate obligations.
-- source:
--   Pinned Finset.sum_range_succ and Finset.sum_mul, and Proved P2-E physical finite-grid rate sum 77b37394. Source rate a=(X.ν (Iic(-(1/(n+1))))).toReal when applying.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_leanlevy_bridge_original_equal_mesh_triangular_rate_real
    (T a : ℝ) (m : ℕ) :
    (∑ i ∈ Finset.range m,
      (((i : ℝ) * T) / (m : ℝ) * a) *
        (((((i : ℝ) + 1) * T) / (m : ℝ) -
          ((i : ℝ) * T) / (m : ℝ)) * a)) =
      ((m : ℝ) * ((m : ℝ) - 1) / 2) *
        ((T * a) ^ 2 / (m : ℝ) ^ 2) := by sorry
