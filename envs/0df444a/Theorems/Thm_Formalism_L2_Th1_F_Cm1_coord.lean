-- Prove2me | Theorems.Thm_Formalism_L2_Th1_F_Cm1_coord
-- name    : Formalism.L2.Th1.F.Cm1.coord
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:57:45.719286+00:00
-- url     : https://prove2.me/theorems/2e09404a-ae13-4c61-8cac-563e74d51192
-- title:
--   Cm1: coord
-- statement:
--   The Cm1 construction uses the coord property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/CmAlternatingForm.lean#L54-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/CmAlternatingForm.lean#L54-L77

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_CMQuasiPeriodConst
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_CmAlternatingForm
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
open Formalism.L2.Th1.F.Cm1

theorem Formalism.L2.Th1.F.Cm1.coord (a : ℕ) (b : ℤ) (d : ℕ) (ha : 0 < a) (hd : 0 < d) (x y : ℝ)
    (h : (x : ℂ) * (a : ℂ) + (y : ℂ) * cmTheta b d = 0) : x = 0 ∧ y = 0 := by sorry
