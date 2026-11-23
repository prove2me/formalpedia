-- Prove2me | Theorems.Thm_Formalism_L2_Th1_F_Cm2_even_im_hermitian_sub
-- name    : Formalism.L2.Th1.F.Cm2.even_im_hermitian_sub
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:15:26.455517+00:00
-- url     : https://prove2.me/theorems/453a115f-c222-43f0-9636-1629079ef4ad
-- title:
--   Cm2: even im hermitian sub
-- statement:
--   The Cm2 construction uses the even im hermitian sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/FormEvenIff.lean#L39-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/FormEvenIff.lean#L39-L64

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_QuasiPeriodConstUnique
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_CmAlternatingForm
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_FormEvenIff
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

theorem Formalism.L2.Th1.F.Cm2.even_im_hermitian_sub (a : ℕ) (b c : ℤ) (d : ℕ) (h : 4 * (a : ℤ) * c = b ^ 2 + d) (hodd : Odd a) (hd8 : d % 8 = 7) :
    Odd b ∧ Even c := by sorry
