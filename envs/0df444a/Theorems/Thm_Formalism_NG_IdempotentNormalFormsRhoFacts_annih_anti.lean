-- Prove2me | Theorems.Thm_Formalism_NG_IdempotentNormalFormsRhoFacts_annih_anti
-- name    : Formalism.NG.IdempotentNormalFormsRhoFacts.annih_anti
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T11:52:03.416342+00:00
-- url     : https://prove2.me/theorems/acf27abc-2412-55b1-8597-5d9450341f21
-- title:
--   Idempotent Normal Forms Rho Facts: annih anti
-- statement:
--   The Idempotent Normal Forms Rho Facts construction uses the annih anti property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/IdempotentNormalForms/LengthEqKerAddRange.lean#L30-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/IdempotentNormalForms/LengthEqKerAddRange.lean#L30-L33

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

theorem Formalism.NG.IdempotentNormalFormsRhoFacts.annih_anti {O Cw Cs P : Type*} [CommRing O] [AddCommGroup Cw] [Module O Cw]
    [AddCommGroup Cs] [Module O Cs] [AddCommGroup P] [Module O P] (pr : Cw →ₗ[O] Cs →ₗ[O] P)
    {U V : Submodule O Cs} (h : U ≤ V) : annih pr V ≤ annih pr U := by sorry
