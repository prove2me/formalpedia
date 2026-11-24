-- Prove2me | Theorems.Thm_Formalism_L2_Th1_F_Hk1_hk_smul
-- name    : Formalism.L2.Th1.F.Hk1.hk_smul
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T21:31:08.302248+00:00
-- url     : https://prove2.me/theorems/6d5900d1-2403-47f6-85d4-1f448945344d
-- title:
--   Hk1: hk smul
-- statement:
--   The Hk1 construction uses the hk smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/HeckeKernelIntegralValue.lean#L49-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/HeckeKernelIntegralValue.lean#L49-L56

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_HkRowIntegral
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_HeckeKernelIntegralValue
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
open MeasureTheory Filter Topology
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
open Formalism.L2.Th1.F.Hk1

theorem Formalism.L2.Th1.F.Hk1.hk_smul (s a : ℝ) (ha : 0 < a) (w : ℂ) :
    hk s ((a : ℂ) * w) = ((a ^ (-(2 + 2 * s)) : ℝ) : ℂ) * hk s w := by sorry
