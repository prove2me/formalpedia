-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_b_rate_real_to_ennreal_normalised_moment_tendsto
-- name    : AvramDividend.Classical.avram_p2_b_rate_real_to_ennreal_normalised_moment_tendsto
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T22:13:21.113284+00:00
-- url     : https://prove2.me/theorems/2b5d742e-04d1-4527-88e1-136a265310fd
-- title:
--   Real small-time rates transport to normalised extended-real moment convergence
-- statement:
--   For a family of finite ENNReal moments at strictly positive time parameters, convergence of the real-valued moment divided by time implies convergence of the corresponding ENNReal moment divided by ofReal time to ofReal of the real limit. The proof uses the pinned ofReal division identity and continuity of the ENNReal ofReal embedding. This provides the common limit-conversion bridge for the original weighted-image law.

import Mathlib.Data.ENNReal.Inv
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Order.Filter.Tendsto

open Filter Topology
open scoped ENNReal

theorem AvramDividend.Classical.avram_p2_b_rate_real_to_ennreal_normalised_moment_tendsto
    {ι : Type*} (l : Filter ι) (a : ι → ℝ≥0∞) (h : ι → ℝ) (m : ℝ)
    (hfinite : ∀ i, a i ≠ ⊤) (hpos : ∀ i, 0 < h i)
    (hlim : Tendsto (fun i => (a i).toReal / h i) l (nhds m)) :
    Tendsto (fun i => a i / ENNReal.ofReal (h i)) l
      (nhds (ENNReal.ofReal m)) := by sorry
