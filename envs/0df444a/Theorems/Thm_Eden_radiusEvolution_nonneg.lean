-- Prove2me | Theorems.Thm_Eden_radiusEvolution_nonneg
-- name    : Eden.radiusEvolution_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:11:42.956019+00:00
-- url     : https://prove2.me/theorems/955d3834-5900-4def-997d-21c822c6fca0
-- title:
--   Eden: radius Evolution nonneg
-- statement:
--   The Eden construction uses the radius Evolution nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/PhysicalRadius.lean#L23-L23
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/PhysicalRadius.lean#L23-L23

import Definitions.Def_Eden_InvariantSets
import Definitions.Def_Eden_GrowthRates
import Definitions.Def_Eden_PhysicalRadius
set_option autoImplicit true
noncomputable section
open Filter Set
open scoped Topology
open Eden

theorem Eden.radiusEvolution_nonneg (t r : ℝ) : 0 ≤ radiusEvolution t r := by sorry
