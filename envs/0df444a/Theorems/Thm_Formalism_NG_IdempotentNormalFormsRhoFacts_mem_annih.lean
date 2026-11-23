-- Prove2me | Theorems.Thm_Formalism_NG_IdempotentNormalFormsRhoFacts_mem_annih
-- name    : Formalism.NG.IdempotentNormalFormsRhoFacts.mem_annih
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:55:26.914368+00:00
-- url     : https://prove2.me/theorems/ae357a65-bb71-4de3-b0f0-2a93826c61f8
-- title:
--   Idempotent Normal Forms Rho Facts: mem annih
-- statement:
--   The Idempotent Normal Forms Rho Facts construction uses the mem annih property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/IdempotentNormalForms/LengthEqKerAddRange.lean#L25-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/IdempotentNormalForms/LengthEqKerAddRange.lean#L25-L28

import Definitions.Def_Formalism_CharacterColumnKernels_StatementRho
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_LengthKerOfDetEqZero
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_RightMulEpsAlgebraMap
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_LengthEqKerAddRange
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
open Formalism.NG.IdempotentNormalFormsRhoFacts

theorem Formalism.NG.IdempotentNormalFormsRhoFacts.mem_annih {O Cw Cs P : Type*} [CommRing O] [AddCommGroup Cw] [Module O Cw]
    [AddCommGroup Cs] [Module O Cs] [AddCommGroup P] [Module O P] (pr : Cw →ₗ[O] Cs →ₗ[O] P)
    (U : Submodule O Cs) (c : Cw) : c ∈ annih pr U ↔ ∀ x ∈ U, pr c x = 0 := by sorry
