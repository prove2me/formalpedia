-- Prove2me | Theorems.Thm_Formalism_NG_QuotientPowerLengths_isTorsionFree_quot
-- name    : Formalism.NG.QuotientPowerLengths.isTorsionFree_quot
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T10:13:57.70658+00:00
-- url     : https://prove2.me/theorems/7f945c41-5e0a-40d9-8999-addbe91dbe1b
-- title:
--   Quotient Power Lengths: is Torsion Free quot
-- statement:
--   The Quotient Power Lengths construction uses the is Torsion Free quot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/IdempotentNormalForms/LengthQuotSmulRangeFree.lean#L183-L190
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/IdempotentNormalForms/LengthQuotSmulRangeFree.lean#L183-L190

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

theorem Formalism.NG.QuotientPowerLengths.isTorsionFree_quot (U : Submodule (FractionRing O) V) : IsTorsionFree O (V ⧸ U) := by sorry
