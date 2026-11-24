-- Prove2me | Theorems.Thm_Formalism_NG_QuotientPowerLengths_cc_mem_VS
-- name    : Formalism.NG.QuotientPowerLengths.cc_mem_VS
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T18:36:43.10263+00:00
-- url     : https://prove2.me/theorems/aa658611-9d57-4eae-9eff-66c326d6f182
-- title:
--   Quotient Power Lengths: cc mem VS
-- statement:
--   The Quotient Power Lengths construction uses the cc mem VS property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/IdempotentNormalForms/LengthQuotSmulRangeFree.lean#L540-L548
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/IdempotentNormalForms/LengthQuotSmulRangeFree.lean#L540-L548

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

theorem Formalism.NG.QuotientPowerLengths.cc_mem_VS (hsum : (⨆ x, Vx T act x) = ⊤) {Z : Set X} {c : T} (hc : c ∈ ccIdeal T Z)
    (v : V) : act c v ∈ VS T act Z := by sorry
