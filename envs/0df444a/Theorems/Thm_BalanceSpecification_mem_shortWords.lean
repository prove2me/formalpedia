-- Prove2me | Theorems.Thm_BalanceSpecification_mem_shortWords
-- name    : BalanceSpecification.mem_shortWords
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:32:06.264856+00:00
-- url     : https://prove2.me/theorems/e71ddf17-489d-4874-892a-bce4ce61ed2d
-- title:
--   Balance Specification: mem short Words
-- statement:
--   The Balance Specification construction uses the mem short Words property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/Specification.lean#L24-L32
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/Specification.lean#L24-L32

module
public import Definitions.Def_BalanceSpecificaton_CountBounds
public import Definitions.Def_BalanceSpecificaton_LanguageProperties
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_Specification
set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification
variable {A : Type*} [Fintype A] {L : Set (Word A)}

theorem BalanceSpecification.mem_shortWords {w : Word A} {N : ℕ} :
    w ∈ shortWords N ↔ w.length ≤ N := by sorry
