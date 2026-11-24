-- Prove2me | Theorems.Thm_BalanceSpecification_periodicConfiguration_shift
-- name    : BalanceSpecification.periodicConfiguration_shift
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:34:29.618937+00:00
-- url     : https://prove2.me/theorems/cde3c601-1314-4687-b381-46986dd0a5a7
-- title:
--   Balance Specification: periodic Configuration shift
-- statement:
--   The Balance Specification construction uses the periodic Configuration shift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/Coded.lean#L93-L97
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/Coded.lean#L93-L97

module
public import Definitions.Def_BalanceSpecificaton_LanguageProperties
public import Mathlib.Topology.Continuous
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_Coded
set_option autoImplicit true
@[expose] public section
public section
open BalanceSpecification
variable {A : Type*}

theorem BalanceSpecification.periodicConfiguration_shift (w : Word A) (hw : 0 < w.length) :
    SymbolicDynamics.FullShift.shift (w.length : ℤ) (periodicConfiguration w hw) =
      periodicConfiguration w hw := by sorry
