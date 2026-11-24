-- Prove2me | Theorems.Thm_Formalism_L2_Th1_F_Hk1_row
-- name    : Formalism.L2.Th1.F.Hk1.row
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T21:31:08.110725+00:00
-- url     : https://prove2.me/theorems/1287d25a-b18c-480b-b42c-6f0329dbcc43
-- title:
--   Hk1: row
-- statement:
--   The Hk1 construction uses the row property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/HeckeKernelIntegralValue.lean#L169-L186
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/HeckeKernelIntegralValue.lean#L169-L186

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

theorem Formalism.L2.Th1.F.Hk1.row (τ : ℂ) (s : ℝ) (n : ℤ) (hτ : τ.im ≠ 0) (hs : 0 ≤ s) (hn : n ≠ 0) :
    Integrable (fun x : ℝ => hk s ((x : ℂ) + (n : ℂ) * τ)) ∧
    hkInt τ s n = (((|(n : ℝ)| * |τ.im|) ^ (-(1 + 2 * s))
      * (hkJ (1 + s) - 2 * hkJ (2 + s)) : ℝ) : ℂ) := by sorry
