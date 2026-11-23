-- Prove2me | Theorems.Thm_Csg_skirmishK_hide_run_throw
-- name    : Csg.skirmishK_hide_run_throw
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T22:29:59.325925+00:00
-- url     : https://prove2.me/theorems/e895ab30-2417-4e70-b08f-b447cbe9508a
-- title:
--   Csg: skirmish K hide run throw
-- statement:
--   The Csg construction uses the skirmish K hide run throw property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/Skirmish.lean#L133-L133
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/Skirmish.lean#L133-L133

import Definitions.Def_Csg_Basic
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Definitions.Def_Csg_Skirmish
set_option autoImplicit true
open Csg

theorem Csg.skirmishK_hide_run_throw : skirmishCSG.K .hide .run .throw = PMF.pure .wet := by sorry
