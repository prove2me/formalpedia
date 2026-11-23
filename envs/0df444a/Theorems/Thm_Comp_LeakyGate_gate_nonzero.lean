-- Prove2me | Theorems.Thm_Comp_LeakyGate_gate_nonzero
-- name    : Comp.LeakyGate.gate_nonzero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T00:17:39.430685+00:00
-- url     : https://prove2.me/theorems/c269adc8-c5f2-458b-8eab-5beaab75013e
-- title:
--   Leaky Gate: gate nonzero
-- statement:
--   No weight is zero -- so a row's keys are its support, which is what keeps the kernel out of
--       the rationals.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/LeakyGateQ.lean#L109-L113
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/LeakyGateQ.lean#L109-L113

import Definitions.Def_Comp_ModelDataQualitative
import Definitions.Def_Comp_LeakyGateQ
set_option autoImplicit true
set_option linter.hashCommand false
open Comp
open Comp.LeakyGate

theorem Comp.LeakyGate.gate_nonzero : gate.Nonzero := by sorry
