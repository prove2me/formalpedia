-- Prove2me | Theorems.Thm_Formalism_NG_QuotientPowerLengths_cc_kill
-- name    : Formalism.NG.QuotientPowerLengths.cc_kill
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T10:13:51.001826+00:00
-- url     : https://prove2.me/theorems/542e6f94-c90a-49a0-a680-6d684d3846b8
-- title:
--   Quotient Power Lengths: cc kill
-- statement:
--   The Quotient Power Lengths construction uses the cc kill property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/IdempotentNormalForms/LengthQuotSmulRangeFree.lean#L530-L535
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/IdempotentNormalForms/LengthQuotSmulRangeFree.lean#L530-L535

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
variable {X : Type*} {T : Subalgebra O (X → O)} {act : T →+* Module.End (FractionRing O) V}

theorem Formalism.NG.QuotientPowerLengths.cc_kill {Z : Set X} {c : T} (hc : c ∈ ccIdeal T Z) :
    VS T act Zᶜ ≤ LinearMap.ker (act c) := by sorry
