-- Prove2me | Theorems.Thm_Formalism_FrobeniusOrbits_EFG_two_isPrime
-- name    : Formalism.FrobeniusOrbits.EFG.two_isPrime
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T14:11:58.132815+00:00
-- url     : https://prove2.me/theorems/6e181caf-4692-4ecc-b4a9-78c7f2e078e8
-- title:
--   EFG: two is Prime
-- statement:
--   The EFG construction uses the two is Prime property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/CardTrivialFirstComponent.lean#L18-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/CardTrivialFirstComponent.lean#L18-L19

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_Statement
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Galois
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_ConjReal
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_CoprimeTwoPow
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_CardTrivialFirstComponent
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_two_isPrime

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

theorem Formalism.FrobeniusOrbits.EFG.two_isPrime : (span {(2 : ℤ)}).IsPrime := by sorry
