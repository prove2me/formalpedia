-- Prove2me | Theorems.Thm_Formalism_NG_QuotientPowerLengths_vx_pres
-- name    : Formalism.NG.QuotientPowerLengths.vx_pres
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:55:13.998499+00:00
-- url     : https://prove2.me/theorems/d6e4af78-3fa3-47ab-b43f-7b39b4ebf336
-- title:
--   Quotient Power Lengths: vx pres
-- statement:
--   The Quotient Power Lengths construction uses the vx pres property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/IdempotentNormalForms/LengthQuotSmulRangeFree.lean#L493-L504
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/IdempotentNormalForms/LengthQuotSmulRangeFree.lean#L493-L504

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

theorem Formalism.NG.QuotientPowerLengths.vx_pres (g : Module.End (FractionRing O) V) (hg : ∀ f : T, g * act f = act f * g) (x : X) :
    Vx T act x ≤ (Vx T act x).comap g := by sorry
