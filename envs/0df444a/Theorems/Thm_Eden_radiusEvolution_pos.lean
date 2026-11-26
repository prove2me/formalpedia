-- Prove2me | Theorems.Thm_Eden_radiusEvolution_pos
-- name    : Eden.radiusEvolution_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:11:43.796449+00:00
-- url     : https://prove2.me/theorems/afddf3d9-1504-4449-aab0-e83a646cf7c8
-- title:
--   Eden: radius Evolution pos
-- statement:
--   The Eden construction uses the radius Evolution pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/PhysicalRadius.lean#L42-L44
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/PhysicalRadius.lean#L42-L44

import Definitions.Def_Eden_InvariantSets
import Definitions.Def_Eden_GrowthRates
import Definitions.Def_Eden_PhysicalRadius
set_option autoImplicit true
noncomputable section
open Filter Set
open scoped Topology
open Eden

theorem Eden.radiusEvolution_pos {t r : ℝ} (ht : 0 ≤ t) (hr : 0 < r) :
    0 < radiusEvolution t r := by sorry
