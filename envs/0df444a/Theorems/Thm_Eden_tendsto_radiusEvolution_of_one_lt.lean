-- Prove2me | Theorems.Thm_Eden_tendsto_radiusEvolution_of_one_lt
-- name    : Eden.tendsto_radiusEvolution_of_one_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:14:35.238391+00:00
-- url     : https://prove2.me/theorems/67661031-e040-4d00-9597-180774dcf83a
-- title:
--   Eden: tendsto radius Evolution of one lt
-- statement:
--   The Eden construction uses the tendsto radius Evolution of one lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/PhysicalRadius.lean#L101-L103
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/PhysicalRadius.lean#L101-L103

import Definitions.Def_Eden_InvariantSets
import Definitions.Def_Eden_GrowthRates
import Definitions.Def_Eden_PhysicalRadius
set_option autoImplicit true
noncomputable section
open Filter Set
open scoped Topology
open Eden

theorem Eden.tendsto_radiusEvolution_of_one_lt {r : ℝ} (hr : 1 < r) :
    Tendsto (fun t => radiusEvolution t r) atTop (𝓝 (Real.sqrt 2)) := by sorry
