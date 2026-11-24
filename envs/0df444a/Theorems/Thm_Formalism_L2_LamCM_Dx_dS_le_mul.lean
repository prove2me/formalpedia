-- Prove2me | Theorems.Thm_Formalism_L2_LamCM_Dx_dS_le_mul
-- name    : Formalism.L2.LamCM.Dx.dS_le_mul
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T22:18:24.490534+00:00
-- url     : https://prove2.me/theorems/d6b0ceca-b03c-41e4-b14d-0095211056eb
-- title:
--   Dx: d S le mul
-- statement:
--   The Dx construction uses the d S le mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CMDeterminantIdeals/CMIdealValuations/AbsNormEqRelIndexMul.lean#L104-L144
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CMDeterminantIdeals/CMIdealValuations/AbsNormEqRelIndexMul.lean#L104-L144

import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CmNumbersLink
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CMIdealValuations_AbsNormEqRelIndexMul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.LamCM
open NumberField IsDedekindDomain
open scoped nonZeroDivisors ComplexOrder
open Formalism.L2.LamCM.Dx
variable {K : Type} [Field K] [NumberField K]

theorem Formalism.L2.LamCM.Dx.dS_le_mul {n : ℕ} (M : Submodule (𝓞 K) (Fin (n+1) → K)) (z : Fin (n+1) → K) (hz1 : z (Fin.last n) = 1)
    (hz : ∀ q ∈ M.map (lastL K n), q • z ∈ M) :
    dS M ≤ dS (M.comap (snocL K n)) * M.map (lastL K n) := by sorry
