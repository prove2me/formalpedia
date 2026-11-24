-- Prove2me | Theorems.Thm_Formalism_NG_QuotientPowerLengths_step1
-- name    : Formalism.NG.QuotientPowerLengths.step1
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T10:15:02.135112+00:00
-- url     : https://prove2.me/theorems/dee5d75c-630b-47b6-8b3b-e4cd89a11be0
-- title:
--   Quotient Power Lengths: step1
-- statement:
--   The Quotient Power Lengths construction uses the step1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/IdempotentNormalForms/LengthQuotSmulRangeFree.lean#L192-L287
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/IdempotentNormalForms/LengthQuotSmulRangeFree.lean#L192-L287

import Definitions.Def_Formalism_CharacterColumnKernels_StatementN
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_LenCokerOfDetNeZero
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_LengthQuotSmulRangeFree
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module IsDiscreteValuationRing
noncomputable section
open Formalism Formalism.NG
open Formalism.NG.QuotientPowerLengths
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
variable {V : Type*} [AddCommGroup V] [Module (FractionRing O) V] [Module O V]
  [IsScalarTower O (FractionRing O) V] [FiniteDimensional (FractionRing O) V]

theorem Formalism.NG.QuotientPowerLengths.step1 (N : Submodule O V) (hN : N.FG) (W U : Submodule (FractionRing O) V)
    (hNWU : N ≤ (W ⊔ U).restrictScalars O) (l : O) :
    Module.length O (N ⧸ (smulRange N l ⊔
      LinearMap.ker ((U.mkQ.restrictScalars O) ∘ₗ N.subtype))) ≤
      (finrank (FractionRing O) W : ℕ∞) * addVal O l := by sorry
