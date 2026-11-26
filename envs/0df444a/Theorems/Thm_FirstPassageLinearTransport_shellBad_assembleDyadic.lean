-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_shellBad_assembleDyadic
-- name    : FirstPassageLinearTransport.shellBad_assembleDyadic
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:11:16.489816+00:00
-- url     : https://prove2.me/theorems/5dba66eb-9c17-417a-be0c-1e82c4d59ec3
-- title:
--   First Passage Linear Transport: shell Bad assemble Dyadic
-- statement:
--   The First Passage Linear Transport construction uses the shell Bad assemble Dyadic property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/VaryingDensity.lean#L26-L36
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/VaryingDensity.lean#L26-L36

import Definitions.Def_FirstPassageLinearTransport_Density
import Definitions.Def_FirstPassageLinearTransport_VaryingDensity
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real Topology BigOperators
noncomputable section

theorem FirstPassageLinearTransport.shellBad_assembleDyadic (S : ℕ → Set ℕ) (M : ℕ) :
    shellBad (assembleDyadic S) M = shellBad (S M) M := by sorry
