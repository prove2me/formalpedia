-- Prove2me | Theorems.Thm_Eden_radiusEvolution_le_max
-- name    : Eden.radiusEvolution_le_max
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T13:14:36.689031+00:00
-- url     : https://prove2.me/theorems/183848ea-f90b-489b-b86f-b5d523e70007
-- title:
--   Eden: radius Evolution le max
-- statement:
--   The Eden construction uses the radius Evolution le max property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/PhysicalRadius.lean#L51-L58
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/PhysicalRadius.lean#L51-L58

import Definitions.Def_Eden_InvariantSets
import Definitions.Def_Eden_GrowthRates
import Definitions.Def_Eden_PhysicalRadius
set_option autoImplicit true
noncomputable section
open Filter Set
open scoped Topology
open Eden

theorem Eden.radiusEvolution_le_max {t r : ℝ} (ht : 0 ≤ t) (hr : 0 ≤ r) :
    radiusEvolution t r ≤ max r (Real.sqrt 2) := by sorry
