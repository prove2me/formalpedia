-- Prove2me | Theorems.Thm_Formalism_L2_Th1_F_Hk1_summable_upper
-- name    : Formalism.L2.Th1.F.Hk1.summable_upper
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T21:30:59.809836+00:00
-- url     : https://prove2.me/theorems/6a52d3cc-971f-45bf-ad49-d937a58368c9
-- title:
--   Hk1: summable upper
-- statement:
--   The Hk1 construction uses the summable upper property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/HeckeKernelIntegralValue.lean#L28-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/HeckeKernelIntegralValue.lean#L28-L37

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

theorem Formalism.L2.Th1.F.Hk1.summable_upper (z : UpperHalfPlane) (s : ℝ) (hs : 0 < s) :
    Summable (fun p : ℤ × ℤ => ‖(p.1 : ℂ) + (p.2 : ℂ) * (z : ℂ)‖ ^ (-(2 + 2 * s))) := by sorry
