-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_shellBad_card_eq_ratio_mul
-- name    : FirstPassageLinearTransport.shellBad_card_eq_ratio_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:11:29.892992+00:00
-- url     : https://prove2.me/theorems/3fc28c27-d96d-4bb5-8211-88187280df60
-- title:
--   First Passage Linear Transport: shell Bad card eq ratio mul
-- statement:
--   The First Passage Linear Transport construction uses the shell Bad card eq ratio mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/VaryingDensity.lean#L47-L51
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/VaryingDensity.lean#L47-L51

import Definitions.Def_FirstPassageLinearTransport_Density
import Definitions.Def_FirstPassageLinearTransport_VaryingDensity
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real Topology BigOperators
noncomputable section

theorem FirstPassageLinearTransport.shellBad_card_eq_ratio_mul (S : Set ℕ) (M : ℕ) :
    ((shellBad S M).card : ℝ) =
      shellExceptionalRatio S M * (2 : ℝ) ^ M := by sorry
