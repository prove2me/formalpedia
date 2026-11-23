-- Prove2me | Theorems.Thm_Formalism_L2_Th1_E_OperatorUThetaLemmas_opU_const_mul
-- name    : Formalism.L2.Th1.E.OperatorUThetaLemmas.opU_const_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:27:07.35188+00:00
-- url     : https://prove2.me/theorems/cd1df28b-c6ea-423e-aa5e-60e99a45cbda
-- title:
--   Operator UTheta Lemmas: op U const mul
-- statement:
--   The Operator UTheta Lemmas construction uses the op U const mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/TorsionTranslationPowers/NonsingularJetNorms/OpUTh0RootOf.lean#L12-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/TorsionTranslationPowers/NonsingularJetNorms/OpUTh0RootOf.lean#L12-L16

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

theorem Formalism.L2.Th1.E.OperatorUThetaLemmas.opU_const_mul (L : PeriodPair) (x a : ℂ) (f : ℂ → ℂ) :
    opU L x (fun z => a * f z) = fun z => a * opU L x f z := by sorry
