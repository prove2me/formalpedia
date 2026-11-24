-- Prove2me | Theorems.Thm_Formalism_FrobeniusOrbits_EFG_coprime_two_pow
-- name    : Formalism.FrobeniusOrbits.EFG.coprime_two_pow
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T14:32:00.867171+00:00
-- url     : https://prove2.me/theorems/4666c72a-4fc9-4c5a-8c3c-6424d810394c
-- title:
--   EFG: coprime two pow
-- statement:
--   The EFG construction uses the coprime two pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/CardTrivialFirstComponent.lean#L49-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/CardTrivialFirstComponent.lean#L49-L51

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_Statement
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Galois
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_ConjReal
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_CoprimeTwoPow
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_CardTrivialFirstComponent
import Theorems.Thm_Formalism_FrobeniusOrbits_Group_coprime_two_pow

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

theorem Formalism.FrobeniusOrbits.EFG.coprime_two_pow {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (e : ℕ) :
    Nat.Coprime p (2 ^ (e + 2)) := by sorry
