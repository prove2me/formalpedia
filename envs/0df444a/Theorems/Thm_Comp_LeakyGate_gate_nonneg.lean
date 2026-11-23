-- Prove2me | Theorems.Thm_Comp_LeakyGate_gate_nonneg
-- name    : Comp.LeakyGate.gate_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T00:46:20.833156+00:00
-- url     : https://prove2.me/theorems/47c6d111-ccad-469c-b067-973ff6128057
-- title:
--   Leaky Gate: gate nonneg
-- statement:
--   No weight is negative.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/LeakyGateQ.lean#L101-L105
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/LeakyGateQ.lean#L101-L105

import Definitions.Def_Comp_ModelDataQualitative
import Definitions.Def_Comp_LeakyGateQ
set_option autoImplicit true
set_option linter.hashCommand false
open Comp
open Comp.LeakyGate

theorem Comp.LeakyGate.gate_nonneg : gate.Nonneg := by sorry
