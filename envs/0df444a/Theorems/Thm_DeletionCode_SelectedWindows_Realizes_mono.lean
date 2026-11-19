-- Prove2me | Theorems.Thm_DeletionCode_SelectedWindows_Realizes_mono
-- name    : DeletionCode.SelectedWindows.Realizes.mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:03:50.290921+00:00
-- url     : https://prove2.me/theorems/7df01750-b1c5-4ee2-a33f-f73c690481ab
-- title:
--   Realizes: mono
-- statement:
--   The Realizes construction uses the mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/SelectedWindows.lean#L146-L150
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/SelectedWindows.lean#L146-L150

import Definitions.Def_DeletionCode_PartialWords
import Definitions.Def_DeletionCode_Recovery
import Definitions.Def_DeletionCode_SelectedWindows
set_option autoImplicit true
open DeletionCode DeletionCode.SelectedWindows
open Windows PartialWords Recovery
variable {B : Type*}

theorem DeletionCode.SelectedWindows.Realizes.mono (s : State B) (mem mem' : B → Memory) (D : B → ℕ) (k : ℕ)
    (hreal : Realizes s mem D k) (hext : ∀ b, Extends (mem b) (mem' b)) :
    Realizes s mem' D k := by sorry
