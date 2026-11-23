-- Prove2me | Theorems.Thm_Formalism_NG_QuotientPowerLengths_split
-- name    : Formalism.NG.QuotientPowerLengths.split
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:14:58.921098+00:00
-- url     : https://prove2.me/theorems/e2672caa-e088-42f1-8fcf-917a543f4613
-- title:
--   Quotient Power Lengths: split
-- statement:
--   The Quotient Power Lengths construction uses the split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/IdempotentNormalForms/LengthQuotSmulRangeFree.lean#L289-L328
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/IdempotentNormalForms/LengthQuotSmulRangeFree.lean#L289-L328

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

theorem Formalism.NG.QuotientPowerLengths.split {M P : Type*} [AddCommGroup M] [Module O M] [AddCommGroup P] [Module O P]
    (A B : Submodule O M) (hAB : A ≤ B) (i : P →ₗ[O] M) (C : Submodule O P)
    (hiB : ∀ p, i p ∈ B) (hC : C ≤ A.comap i) (hB : B ≤ A ⊔ LinearMap.range i) :
    Module.length O (M ⧸ A) ≤ Module.length O (M ⧸ B) + Module.length O (P ⧸ C) := by sorry
