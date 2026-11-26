-- Prove2me | Theorems.Thm_Eden_radiusEvolution_antitoneOn
-- name    : Eden.radiusEvolution_antitoneOn
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:31:33.845415+00:00
-- url     : https://prove2.me/theorems/1c79d3e2-3511-4922-b1b5-5a10948800e3
-- title:
--   Eden: radius Evolution antitone On
-- statement:
--   The Eden construction uses the radius Evolution antitone On property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/PhysicalRadius.lean#L81-L94
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/PhysicalRadius.lean#L81-L94

import Definitions.Def_Eden_InvariantSets
import Definitions.Def_Eden_GrowthRates
import Definitions.Def_Eden_PhysicalRadius
set_option autoImplicit true
noncomputable section
open Filter Set
open scoped Topology
open Eden

theorem Eden.radiusEvolution_antitoneOn {R : ℝ} (hR : Real.sqrt 2 ≤ R) :
    AntitoneOn (fun t => radiusEvolution t R) (Ici 0) := by sorry
