-- Prove2me | Theorems.Thm_Formalism_NG_QuotientPowerLengths_VS_sup_compl
-- name    : Formalism.NG.QuotientPowerLengths.VS_sup_compl
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:55:59.469863+00:00
-- url     : https://prove2.me/theorems/2d2188bb-2ba4-4664-aa32-4b166a7ce9e0
-- title:
--   Quotient Power Lengths: VS sup compl
-- statement:
--   The Quotient Power Lengths construction uses the VS sup compl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/IdempotentNormalForms/LengthQuotSmulRangeFree.lean#L511-L518
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/IdempotentNormalForms/LengthQuotSmulRangeFree.lean#L511-L518

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

theorem Formalism.NG.QuotientPowerLengths.VS_sup_compl (hsum : (⨆ x, Vx T act x) = ⊤) (S : Set X) :
    VS T act S ⊔ VS T act Sᶜ = ⊤ := by sorry
