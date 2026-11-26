-- Prove2me | Theorems.Thm_Eden_radiusEvolution_sq
-- name    : Eden.radiusEvolution_sq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:11:13.954524+00:00
-- url     : https://prove2.me/theorems/ec477bae-8407-59fe-b129-083727e20df0
-- title:
--   Eden: radius Evolution sq
-- statement:
--   The Eden construction uses the radius Evolution sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/PhysicalRadius.lean#L25-L27
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/PhysicalRadius.lean#L25-L27

import Definitions.Def_Eden_InvariantSets
import Definitions.Def_Eden_GrowthRates
import Definitions.Def_Eden_PhysicalRadius
set_option autoImplicit true
noncomputable section
open Filter Set
open scoped Topology
open Eden

theorem Eden.radiusEvolution_sq {t : ℝ} (ht : 0 ≤ t) (r : ℝ) :
    radiusEvolution t r ^ 2 = squaredRadiusEvolution t (r ^ 2) := by sorry
