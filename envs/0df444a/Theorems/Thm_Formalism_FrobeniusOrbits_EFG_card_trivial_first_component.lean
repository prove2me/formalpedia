-- Prove2me | Theorems.Thm_Formalism_FrobeniusOrbits_EFG_card_trivial_first_component
-- name    : Formalism.FrobeniusOrbits.EFG.card_trivial_first_component
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T14:12:28.41202+00:00
-- url     : https://prove2.me/theorems/4c09974e-795b-4ab2-bfcd-b0469e7b344a
-- title:
--   EFG: card trivial first component
-- statement:
--   The EFG construction uses the card trivial first component property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/CardTrivialFirstComponent.lean#L21-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/CardTrivialFirstComponent.lean#L21-L31

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

theorem Formalism.FrobeniusOrbits.EFG.card_trivial_first_component (e : ℕ) : Nat.card {g : GG e // g.1 = 1} = 2 ^ e := by sorry
