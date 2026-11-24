-- Prove2me | Theorems.Thm_Formalism_L2_Th1_F_Cm2_form_even_iff
-- name    : Formalism.L2.Th1.F.Cm2.form_even_iff
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T09:02:08.401556+00:00
-- url     : https://prove2.me/theorems/1ee4ac8c-00a4-490e-bce6-af6df21a9f39
-- title:
--   Cm2: form even iff
-- statement:
--   The Cm2 construction uses the form even iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/FormEvenIff.lean#L66-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/FormEvenIff.lean#L66-L75

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

theorem Formalism.L2.Th1.F.Cm2.form_even_iff (a b c m n : ℤ) (ha : Odd a) (hb : Odd b) (hc : Even c) :
    Even (cmForm a b c m n) ↔ (Even m ∨ Odd n) := by sorry
