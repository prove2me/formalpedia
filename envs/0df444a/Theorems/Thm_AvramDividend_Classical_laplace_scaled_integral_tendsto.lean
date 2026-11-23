-- Prove2me | Theorems.Thm_AvramDividend_Classical_laplace_scaled_integral_tendsto
-- name    : AvramDividend.Classical.laplace_scaled_integral_tendsto
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T19:24:03.02201+00:00
-- url     : https://prove2.me/theorems/c643cff4-e58d-480a-bc94-3ab7d21bbb9d
-- title:
--   Scaled Laplace integral converges to the scale origin
-- statement:
--   For a nonnegative continuous monotone scale function, the exponentially weighted integral of s(u/beta) tends to s(0), dominated at any positive frequency for which the Laplace integral is finite.
-- source:
--   Lemma 8.6 corrected proof: dominated convergence for the Laplace approximate identity.

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
set_option autoImplicit false
open MeasureTheory Filter Set Topology Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal

theorem AvramDividend.Classical.laplace_scaled_integral_tendsto
    (s : ℝ → ℝ) (βstar : ℝ) (hβstar : 0 < βstar)
    (hnonneg : ∀ x : ℝ, 0 ≤ x → 0 ≤ s x)
    (hcont : ContinuousOn s (Set.Ici (0 : ℝ)))
    (hmono : MonotoneOn s (Set.Ici (0 : ℝ)))
    (hInt : IntegrableOn (fun x : ℝ => Real.exp (-βstar * x) * s x) (Set.Ioi 0) volume) :
    Tendsto (fun β : ℝ => ∫ u in Set.Ioi (0 : ℝ), Real.exp (-u) * s (u / β)) atTop
      (𝓝 (s 0)) := by sorry
