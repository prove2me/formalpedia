-- Prove2me | Theorems.Thm_Formalism_NG_gen_relMap_mul
-- name    : Formalism.NG.gen_relMap_mul
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T10:15:48.189269+00:00
-- url     : https://prove2.me/theorems/28cec037-8b5a-4037-9628-71b3b20291ed
-- title:
--   NG: gen rel Map mul
-- statement:
--   The NG construction uses the gen rel Map mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/IdempotentNormalForms/GenRelMapApply.lean#L16-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/IdempotentNormalForms/GenRelMapApply.lean#L16-L22

import Definitions.Def_Formalism_CharacterColumnKernels_StatementG
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_GenRelMapApply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.NG
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

theorem Formalism.NG.gen_relMap_mul {a b c : Type*} [Fintype a] [Fintype b] [Fintype c]
    (X : Matrix a b O) (Y : Matrix b c O) :
    relMap O (KO O) (X * Y) = relMap O (KO O) X ∘ₗ relMap O (KO O) Y := by sorry
