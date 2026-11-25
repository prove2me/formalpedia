-- Prove2me | Theorems.Thm_Formalism_IndefR_LiftF_IsAdjOf_unique
-- name    : Formalism.IndefR.LiftF.IsAdjOf.unique
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T11:45:01.997268+00:00
-- url     : https://prove2.me/theorems/7184144f-4db4-55f2-aa1b-44e6572d5eb5
-- title:
--   Is Adj Of: unique
-- statement:
--   The Is Adj Of construction uses the unique property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/HasInfExpF.lean#L82-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/HasInfExpF.lean#L82-L86

import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_DatumF
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_HasInfExpF
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory
open Formalism Formalism.IndefR Formalism.IndefR.LiftF
variable {M N : Type*} [AddCommGroup M] [Module ℂ M] [AddCommGroup N] [Module ℂ N]

theorem Formalism.IndefR.LiftF.IsAdjOf.unique {ipM : M →ₗ[ℂ] M →ₗ⋆[ℂ] ℂ} {ipN : N →ₗ[ℂ] N →ₗ⋆[ℂ] ℂ} {A : M →ₗ[ℂ] N}
    {B B' : N →ₗ[ℂ] M} (hnd : ∀ z, (∀ x, ipM x z = 0) → z = 0)
    (h : IsAdjOf ipM ipN A B) (h' : IsAdjOf ipM ipN A B') : B = B' := by sorry
