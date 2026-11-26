-- Prove2me | Theorems.Thm_Eden_infDist_attractor_sq_le
-- name    : Eden.infDist_attractor_sq_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:38:21.121851+00:00
-- url     : https://prove2.me/theorems/be866656-5720-44f1-9041-d3bd2e5bb6f6
-- title:
--   Eden: inf Dist attractor sq le
-- statement:
--   The Eden construction uses the inf Dist attractor sq le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/AttractorDistance.lean#L82-L89
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/AttractorDistance.lean#L82-L89

import Definitions.Def_Eden_InvariantSets
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Definitions.Def_Eden_AttractorDistance
set_option autoImplicit true
noncomputable section
open Eden

theorem Eden.infDist_attractor_sq_le (p : PhaseSpace) :
    Metric.infDist p attractor ^ 2 ≤
      max (Real.sqrt (radiusSq₁ p) - Real.sqrt 2) 0 ^ 2 +
      max (Real.sqrt (radiusSq₂ p) - Real.sqrt 2) 0 ^ 2 + p 4 ^ 2 := by sorry
