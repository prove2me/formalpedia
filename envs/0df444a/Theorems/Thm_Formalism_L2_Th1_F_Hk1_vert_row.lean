-- Prove2me | Theorems.Thm_Formalism_L2_Th1_F_Hk1_vert_row
-- name    : Formalism.L2.Th1.F.Hk1.vert_row
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T21:30:44.522897+00:00
-- url     : https://prove2.me/theorems/5adfabff-7e06-402c-bd87-c7f9915b41ae
-- title:
--   Hk1: vert row
-- statement:
--   The Hk1 construction uses the vert row property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/HeckeKernelIntegralValue.lean#L137-L167
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/HeckeKernelIntegralValue.lean#L137-L167

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

theorem Formalism.L2.Th1.F.Hk1.vert_row (s c : ℝ) (hs : 0 ≤ s) (hc : c ≠ 0) :
    Integrable (fun x : ℝ => hk s ((x : ℂ) + (c : ℂ) * Complex.I)) ∧
    ∫ x : ℝ, hk s ((x : ℂ) + (c : ℂ) * Complex.I)
      = ((|c| ^ (-(1 + 2 * s)) * (hkJ (1 + s) - 2 * hkJ (2 + s)) : ℝ) : ℂ) := by sorry
