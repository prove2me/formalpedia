-- Prove2me | Theorems.Thm_Formalism_L2_Th1_F_Hk2_hk_cont
-- name    : Formalism.L2.Th1.F.Hk2.hk_cont
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T21:31:00.038203+00:00
-- url     : https://prove2.me/theorems/7b325f8a-21a5-4cd9-8b71-ec5f05039679
-- title:
--   Hk2: hk cont
-- statement:
--   The Hk2 construction uses the hk cont property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/HeckeKernelCellContinuous.lean#L177-L185
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/HeckeKernelCellContinuous.lean#L177-L185

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_HkRowIntegral
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_HeckeKernelCellContinuous
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
open Formalism.L2.Th1.F.Hk2

theorem Formalism.L2.Th1.F.Hk2.hk_cont {τ : ℂ} (hτ : τ.im ≠ 0) {n : ℤ} (hn : n ≠ 0) (m : ℤ) :
    Continuous (Function.uncurry fun (s x : ℝ) => hk s ((m : ℂ) + (x : ℂ) + (n : ℂ) * τ)) := by sorry
