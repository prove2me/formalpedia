-- Prove2me | Theorems.Thm_Formalism_L2_Th1_F_Hk1_hk_unit
-- name    : Formalism.L2.Th1.F.Hk1.hk_unit
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T21:30:43.264908+00:00
-- url     : https://prove2.me/theorems/42e7ed1b-7abc-47ba-8da1-e4db073a8f9b
-- title:
--   Hk1: hk unit
-- statement:
--   The Hk1 construction uses the hk unit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/HeckeKernelIntegralValue.lean#L58-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/HeckeKernelIntegralValue.lean#L58-L89

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

theorem Formalism.L2.Th1.F.Hk1.hk_unit (s t ε : ℝ) (hε : ε ^ 2 = 1) :
    hk s ((t : ℂ) + (ε : ℂ) * Complex.I) =
      (((1 + t ^ 2) ^ (-(1 + s)) - 2 * (1 + t ^ 2) ^ (-(2 + s)) : ℝ) : ℂ)
        - 2 * ε * Complex.I * ((t * (1 + t ^ 2) ^ (-(2 + s)) : ℝ) : ℂ) := by sorry
