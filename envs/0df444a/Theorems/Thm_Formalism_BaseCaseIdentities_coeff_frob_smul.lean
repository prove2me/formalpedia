-- Prove2me | Theorems.Thm_Formalism_BaseCaseIdentities_coeff_frob_smul
-- name    : Formalism.BaseCaseIdentities.coeff_frob_smul
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T00:19:22.7965+00:00
-- url     : https://prove2.me/theorems/dfada04d-27b5-410f-8864-2f7ae28de0b9
-- title:
--   Base Case Identities: coeff frob smul
-- statement:
--   The Base Case Identities construction uses the coeff frob smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusBaseCase/FrobeniusBaseCaseProofs/BaseCaseKOneHolds.lean#L109-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusBaseCase/FrobeniusBaseCaseProofs/BaseCaseKOneHolds.lean#L109-L117

import Definitions.Def_Formalism_FrobeniusBaseCase_Statement
import Definitions.Def_Formalism_FrobeniusBaseCase_FrobeniusBaseCaseProofs_BaseCaseKOneHolds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPowerSeries
open Formalism Formalism.BaseCaseIdentities
noncomputable section
open Classical

theorem Formalism.BaseCaseIdentities.coeff_frob_smul {k : Type*} [Field k] {Z : Type*} (N : ℕ) (hN : 1 ≤ N)
    (f : MvPowerSeries Z k) (A : Z →₀ ℕ) : coeff (N • A) (frob N f) = (coeff A f) ^ N := by sorry
