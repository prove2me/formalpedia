-- Prove2me | Theorems.Thm_Eden_radiusEvolution_at_zero
-- name    : Eden.radiusEvolution_at_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:10:47.003971+00:00
-- url     : https://prove2.me/theorems/d250fc55-64de-48c1-9253-cff4dedebcc1
-- title:
--   Eden: radius Evolution at zero
-- statement:
--   The Eden construction uses the radius Evolution at zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/PhysicalRadius.lean#L32-L33
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/PhysicalRadius.lean#L32-L33

import Definitions.Def_Eden_InvariantSets
import Definitions.Def_Eden_GrowthRates
import Definitions.Def_Eden_PhysicalRadius
set_option autoImplicit true
noncomputable section
open Filter Set
open scoped Topology
open Eden

theorem Eden.radiusEvolution_at_zero (t : ℝ) : radiusEvolution t 0 = 0 := by sorry
