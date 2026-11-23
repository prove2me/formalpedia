-- Prove2me | Theorems.Thm_Formalism_L2_Th1_F_Cm2_exp_pi_int
-- name    : Formalism.L2.Th1.F.Cm2.exp_pi_int
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:13:02.954323+00:00
-- url     : https://prove2.me/theorems/08f23500-5c46-4f97-9d9f-bc77472dbbc7
-- title:
--   Cm2: exp pi int
-- statement:
--   The Cm2 construction uses the exp pi int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/FormEvenIff.lean#L77-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/FormEvenIff.lean#L77-L85

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_QuasiPeriodConstUnique
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_CmAlternatingForm
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_FormEvenIff
import Theorems.Thm_Formalism_L2_Th1_F_PeriodAreaSignLemmas_exp_pi_int
import Theorems.Thm_Formalism_L2_Th1_F_ThetaZeroHermitianLemmas_exp_pi_int

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
open Formalism.L2.Th1.F.Cm2
open Cm1

theorem Formalism.L2.Th1.F.Cm2.exp_pi_int (n : ℤ) :
    Complex.exp ((Real.pi : ℂ) * Complex.I * (((n : ℤ) : ℝ) : ℂ)) = if Even n then 1 else -1 := by sorry
