-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_mem_prefixBad
-- name    : FirstPassageLinearTransport.mem_prefixBad
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:56:43.134913+00:00
-- url     : https://prove2.me/theorems/b004f3f6-d28a-4b5d-b697-b7d5e37935e5
-- title:
--   First Passage Linear Transport: mem prefix Bad
-- statement:
--   The First Passage Linear Transport construction uses the mem prefix Bad property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/Density.lean#L120-L123
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/Density.lean#L120-L123

import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Definitions.Def_FirstPassageLinearTransport_Basic
import Definitions.Def_FirstPassageLinearTransport_Density
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real
noncomputable section

theorem FirstPassageLinearTransport.mem_prefixBad {S : Set ℕ} {X n : ℕ} :
    n ∈ prefixBad S X ↔ 1 ≤ n ∧ n ≤ X ∧ n ∉ S := by sorry
