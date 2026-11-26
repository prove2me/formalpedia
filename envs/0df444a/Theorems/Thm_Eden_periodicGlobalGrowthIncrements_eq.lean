-- Prove2me | Theorems.Thm_Eden_periodicGlobalGrowthIncrements_eq
-- name    : Eden.periodicGlobalGrowthIncrements_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:37:47.671451+00:00
-- url     : https://prove2.me/theorems/bccfdfda-2e11-506f-a0d5-65199399ecc9
-- title:
--   Eden: periodic Global Growth Increments eq
-- statement:
--   The Eden construction uses the periodic Global Growth Increments eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/PeriodicGlobalDimension.lean#L28-L33
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/PeriodicGlobalDimension.lean#L28-L33

import Definitions.Def_Eden_PeriodicGlobalGrowth
import Definitions.Def_Eden_PeriodicGlobalDimension
set_option autoImplicit true
noncomputable section
open Set
open Eden

theorem Eden.periodicGlobalGrowthIncrements_eq {c : ℝ} (hc : 4 < c) :
    periodicGlobalGrowthIncrements c = ![2, 0, -2, -2, -c] := by sorry
