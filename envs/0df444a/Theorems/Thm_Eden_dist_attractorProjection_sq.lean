-- Prove2me | Theorems.Thm_Eden_dist_attractorProjection_sq
-- name    : Eden.dist_attractorProjection_sq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:12:26.234466+00:00
-- url     : https://prove2.me/theorems/93fb5d64-0a3d-5e68-bd55-48a8fcc74df5
-- title:
--   Eden: dist attractor Projection sq
-- statement:
--   The Eden construction uses the dist attractor Projection sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/AttractorDistance.lean#L70-L80
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/AttractorDistance.lean#L70-L80

import Definitions.Def_Eden_InvariantSets
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Definitions.Def_Eden_AttractorDistance
set_option autoImplicit true
noncomputable section
open Eden

theorem Eden.dist_attractorProjection_sq (p : PhaseSpace) :
    dist p (attractorProjection p) ^ 2 =
      max (Real.sqrt (radiusSq₁ p) - Real.sqrt 2) 0 ^ 2 +
      max (Real.sqrt (radiusSq₂ p) - Real.sqrt 2) 0 ^ 2 + p 4 ^ 2 := by sorry
