-- Prove2me | Theorems.Thm_Eden_evolution_origin
-- name    : Eden.evolution_origin
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:44:37.312461+00:00
-- url     : https://prove2.me/theorems/82790772-b6ee-4e49-82d7-1b6358f8a52d
-- title:
--   Eden: evolution origin
-- statement:
--   The Eden construction uses the evolution origin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/PeriodicSets.lean#L36-L38
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/PeriodicSets.lean#L36-L38

import Definitions.Def_Eden_RotationReturns
import Definitions.Def_Eden_PeriodicSets
set_option autoImplicit true
noncomputable section
open Set
open Eden

theorem Eden.evolution_origin (c t : ℝ) : evolution c t 0 = 0 := by sorry
