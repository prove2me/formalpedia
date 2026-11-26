-- Prove2me | Theorems.Thm_Eden_discScale_distance_sq
-- name    : Eden.discScale_distance_sq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:12:18.685538+00:00
-- url     : https://prove2.me/theorems/fafa21e3-288e-5de5-bb02-3a637c1b8cb2
-- title:
--   Eden: disc Scale distance sq
-- statement:
--   The Eden construction uses the disc Scale distance sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/AttractorDistance.lean#L40-L58
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/AttractorDistance.lean#L40-L58

import Definitions.Def_Eden_InvariantSets
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Definitions.Def_Eden_AttractorDistance
set_option autoImplicit true
noncomputable section
open Eden

theorem Eden.discScale_distance_sq (x y : ℝ) :
    (x - discScale (Real.sqrt (x ^ 2 + y ^ 2)) * x) ^ 2 +
      (y - discScale (Real.sqrt (x ^ 2 + y ^ 2)) * y) ^ 2 =
      max (Real.sqrt (x ^ 2 + y ^ 2) - Real.sqrt 2) 0 ^ 2 := by sorry
