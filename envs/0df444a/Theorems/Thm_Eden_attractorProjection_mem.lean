-- Prove2me | Theorems.Thm_Eden_attractorProjection_mem
-- name    : Eden.attractorProjection_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:12:26.350784+00:00
-- url     : https://prove2.me/theorems/04d4678b-ab22-4262-bde7-873237db99e1
-- title:
--   Eden: attractor Projection mem
-- statement:
--   The Eden construction uses the attractor Projection mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/AttractorDistance.lean#L67-L68
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/AttractorDistance.lean#L67-L68

import Definitions.Def_Eden_InvariantSets
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Definitions.Def_Eden_AttractorDistance
set_option autoImplicit true
noncomputable section
open Eden

theorem Eden.attractorProjection_mem (p : PhaseSpace) : attractorProjection p ∈ attractor := by sorry
