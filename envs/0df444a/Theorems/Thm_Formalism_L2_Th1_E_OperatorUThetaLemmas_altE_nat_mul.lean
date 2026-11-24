-- Prove2me | Theorems.Thm_Formalism_L2_Th1_E_OperatorUThetaLemmas_altE_nat_mul
-- name    : Formalism.L2.Th1.E.OperatorUThetaLemmas.altE_nat_mul
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:53:42.067076+00:00
-- url     : https://prove2.me/theorems/ae20d325-5e8f-4ba2-83b2-e3842305d3ad
-- title:
--   Operator UTheta Lemmas: alt E nat mul
-- statement:
--   The Operator UTheta Lemmas construction uses the alt E nat mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/TorsionTranslationPowers/NonsingularJetNorms/OpUTh0RootOf.lean#L18-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/TorsionTranslationPowers/NonsingularJetNorms/OpUTh0RootOf.lean#L18-L24

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_StatementA
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_QuasiPeriodConstUnique
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_NonsingularJetNorms_OpUTh0RootOf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ComplexConjugate
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.E
open Formalism.L2.Th1.E.OperatorUThetaLemmas
open Formalism.L2.Th1.F

theorem Formalism.L2.Th1.E.OperatorUThetaLemmas.altE_nat_mul (L : PeriodPair) (N : ℕ) (x y : ℂ) :
    altE L ((N : ℂ) * x) ((N : ℂ) * y) = (N : ℝ) ^ 2 * altE L x y := by sorry
