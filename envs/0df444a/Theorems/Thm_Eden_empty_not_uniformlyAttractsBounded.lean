-- Prove2me | Theorems.Thm_Eden_empty_not_uniformlyAttractsBounded
-- name    : Eden.empty_not_uniformlyAttractsBounded
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:39:48.214006+00:00
-- url     : https://prove2.me/theorems/7cb91cb4-c700-4440-9fa9-f7b37524229f
-- title:
--   Eden: empty not uniformly Attracts Bounded
-- statement:
--   The Eden construction uses the empty not uniformly Attracts Bounded property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/UniformAttraction.lean#L163-L166
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/UniformAttraction.lean#L163-L166

import Definitions.Def_Eden_PhysicalRadius
import Definitions.Def_Eden_AttractorDistance
import Definitions.Def_Eden_StrictInvariance
import Definitions.Def_Eden_UniformAttraction
set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden

theorem Eden.empty_not_uniformlyAttractsBounded (c : ℝ) :
    ¬UniformlyAttractsBounded c (∅ : Set PhaseSpace) := by sorry
