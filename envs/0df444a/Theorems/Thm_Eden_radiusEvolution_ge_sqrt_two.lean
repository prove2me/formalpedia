-- Prove2me | Theorems.Thm_Eden_radiusEvolution_ge_sqrt_two
-- name    : Eden.radiusEvolution_ge_sqrt_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:11:26.974207+00:00
-- url     : https://prove2.me/theorems/5209e6ed-2ce4-4e8e-bb79-86fc960daab3
-- title:
--   Eden: radius Evolution ge sqrt two
-- statement:
--   The Eden construction uses the radius Evolution ge sqrt two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/PhysicalRadius.lean#L60-L62
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/PhysicalRadius.lean#L60-L62

import Definitions.Def_Eden_InvariantSets
import Definitions.Def_Eden_GrowthRates
import Definitions.Def_Eden_PhysicalRadius
set_option autoImplicit true
noncomputable section
open Filter Set
open scoped Topology
open Eden

theorem Eden.radiusEvolution_ge_sqrt_two {t R : ℝ} (ht : 0 ≤ t) (hR : Real.sqrt 2 ≤ R) :
    Real.sqrt 2 ≤ radiusEvolution t R := by sorry
