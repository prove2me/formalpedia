-- Prove2me | Theorems.Thm_FairSelling_ElevenTwelfths_eleven_twelfths_gap
-- name    : FairSelling.ElevenTwelfths.eleven_twelfths_gap
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T03:18:57.991819+00:00
-- url     : https://prove2.me/theorems/0b033616-ba25-46b8-97cb-7a75405c3f5d
-- title:
--   Eleven Twelfths: eleven twelfths gap
-- statement:
--   **Proposition 1**, packaged: for every `ρ > 11/12` there is an allocation instance with
--   `n = 3` agents and `m = 8` goods (non-negative additive valuations, non-negative prices) in
--   which no valid outcome gives every agent `ρ` times her maximin share with selling.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ElevenTwelfths.lean#L313-L321
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ElevenTwelfths.lean#L313-L321

import Mathlib
import Definitions.Def_RequestProject_ThreeAgents
import Definitions.Def_RequestProject_FeigeNorkin
import Definitions.Def_RequestProject_ElevenTwelfths
set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.ElevenTwelfths
open FeigeNorkin

theorem FairSelling.ElevenTwelfths.eleven_twelfths_gap {ρ : ℝ} (hρ : 11/12 < ρ) :
    ∃ (v : Fin 3 → Fin 8 → ℝ) (p : Fin 8 → ℝ),
      (∀ i g, 0 ≤ v i g) ∧ (∀ g, 0 ≤ p g) ∧
      ∀ o : Outcome (Fin 8) 3, o.Valid p →
        ∃ i, util (v i) o i < ρ * MMS 3 (v i) p := by sorry
