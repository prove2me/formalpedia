-- Prove2me | Theorems.Thm_FairSelling_ElevenTwelfths_cast_sum_eq
-- name    : FairSelling.ElevenTwelfths.cast_sum_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:28:55.130207+00:00
-- url     : https://prove2.me/theorems/243e5e1c-acfe-4712-ad09-788a2a45d2f6
-- title:
--   Eleven Twelfths: cast sum eq
-- statement:
--   Casting a natural-number bundle value to `ℝ`.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ElevenTwelfths.lean#L46-L48
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ElevenTwelfths.lean#L46-L48

import Mathlib
import Definitions.Def_RequestProject_ThreeAgents
import Definitions.Def_RequestProject_FeigeNorkin
import Definitions.Def_RequestProject_ElevenTwelfths
set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.ElevenTwelfths
open FeigeNorkin

theorem FairSelling.ElevenTwelfths.cast_sum_eq (s : Finset (Fin 8)) (w : Fin 8 → ℕ) (m : ℕ) (h : ∑ g ∈ s, w g = m) :
    ∑ g ∈ s, (w g : ℝ) = m := by sorry
