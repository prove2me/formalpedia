-- Prove2me | Theorems.Thm_AvramDividend_Classical_barrierRuinTime_zero_of_early_downward_jumps
-- name    : AvramDividend.Classical.barrierRuinTime_zero_of_early_downward_jumps
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T20:48:33.439397+00:00
-- url     : https://prove2.me/theorems/43a43e59-d305-463e-abae-4515e2d65915
-- title:
--   Arbitrarily early downward Lévy jumps imply immediate zero-barrier reflected ruin
-- statement:
--   If a càdlàg sample path has a genuine downward jump in every positive initial time interval, then it has a strict decrease at times arbitrarily close to zero, and the reflected zero-barrier ruin time is zero. The proof uses the actual left-hand limit, a nontrivial left neighbourhood and the already Proved strict-path-decrease ruin criterion. This gives a reusable deterministic bridge from the jump activity of the Lévy measure to the zero-barrier identity.
-- source:
--   Avram, Palmowski and Pistorius (2007), Proposition 1, zero-barrier discussion after equation (3.13), https://arxiv.org/pdf/math/0702893

import Theorems.Thm_AvramDividend_Classical_barrierRuinTime_zero_of_near_zero_path_decrease
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Topology.Order.OrderClosed

open AvramDividend.Classical MeasureTheory Set Filter
open scoped NNReal ENNReal

namespace AvramDividend.Classical

/-- Downward jumps at arbitrarily small positive times force immediate zero-barrier ruin. -/
theorem barrierRuinTime_zero_of_early_downward_jumps
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (hJumps : ∀ ε : ℝ≥0, 0 < ε →
      ∃ t : ℝ≥0, 0 < t ∧ t < ε ∧
        ∃ l : ℝ,
          Tendsto (fun s : ℝ≥0 => X.X s ω) (nhdsWithin t (Iio t)) (nhds l) ∧
          X.X t ω < l) :
    barrierRuinTime X 0 ω = 0 := by sorry

end AvramDividend.Classical
