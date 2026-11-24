-- Prove2me | Theorems.Thm_Formalism_FrobeniusOrbits_EFG_card_Psi
-- name    : Formalism.FrobeniusOrbits.EFG.card_Psi
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T14:10:45.791433+00:00
-- url     : https://prove2.me/theorems/ba206d1d-9d0b-417d-9a60-1f39c8f34d6a
-- title:
--   EFG: card Psi
-- statement:
--   The EFG construction uses the card Psi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/CardTrivialFirstComponent.lean#L33-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/CardTrivialFirstComponent.lean#L33-L47

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_Statement
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Galois
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_ConjReal
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_CoprimeTwoPow
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_CardTrivialFirstComponent
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField Ideal
open scoped Pointwise
noncomputable section
open Formalism Formalism.FrobeniusOrbits
open Formalism.TwoAdicCyclotomicDecomposition
open Formalism.FrobeniusOrbits.EFG

theorem Formalism.FrobeniusOrbits.EFG.card_Psi (e : ℕ) : Nat.card (Psi e) = 2 ^ (e + 1) := by sorry
