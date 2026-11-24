-- Prove2me | Theorems.Thm_FongoSync_merged_batches
-- name    : FongoSync.merged_batches
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T08:03:07.068859+00:00
-- url     : https://prove2.me/theorems/277b30c7-12f3-4603-9ebf-e4e0cb395611
-- title:
--   Fongo Sync: merged batches
-- statement:
--   Two replicas that received the same batches, each in its own order and with repeats, agree.
--
--   Source: https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/State.lean#L170-L173
-- source:
--   https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/State.lean#L170-L173

import Definitions.Def_FongoSync_Register
import Definitions.Def_FongoSync_State
set_option autoImplicit false
open FongoSync
open Std
set_option linter.unusedSectionVars false
variable {V : Type}
variable [Ord V]
variable [TransOrd V] [LawfulEqOrd V]

theorem FongoSync.merged_batches (σ : String → String → Strategy) (b₁ b₂ : List (List (Change V)))
    (same : ∀ b, b ∈ b₁ ↔ b ∈ b₂) (h : ClockDetermines b₁.flatten) :
    merged σ b₁.flatten = merged σ b₂.flatten := by sorry
