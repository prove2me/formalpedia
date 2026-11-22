-- Prove2me | Theorems.Thm_Formalism_NG_IdempotentNormalFormsRhoFacts_length_eq_ker_add_range
-- name    : Formalism.NG.IdempotentNormalFormsRhoFacts.length_eq_ker_add_range
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:06:44.753461+00:00
-- url     : https://prove2.me/theorems/c8cbd199-d859-485f-a4ad-390db4ac9f70
-- title:
--   Idempotent Normal Forms Rho Facts: length eq ker add range
-- statement:
--   The Idempotent Normal Forms Rho Facts construction uses the length eq ker add range property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/IdempotentNormalForms/LengthEqKerAddRange.lean#L13-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/IdempotentNormalForms/LengthEqKerAddRange.lean#L13-L19

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

theorem Formalism.NG.IdempotentNormalFormsRhoFacts.length_eq_ker_add_range {R M P : Type*} [Ring R] [AddCommGroup M] [Module R M]
    [AddCommGroup P] [Module R P] (φ : M →ₗ[R] P) :
    Module.length R M =
      Module.length R (LinearMap.ker φ) + Module.length R (LinearMap.range φ) := by sorry
