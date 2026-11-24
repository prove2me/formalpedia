-- Prove2me | Theorems.Thm_Formalism_L2_Th1_E_Th0Analytic_of
-- name    : Formalism.L2.Th1.E.Th0Analytic_of
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:55:59.893973+00:00
-- url     : https://prove2.me/theorems/acd561af-a486-42e8-b01c-f6a685669248
-- title:
--   E: Th0 Analytic of
-- statement:
--   The E construction uses the Th0 Analytic of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/TorsionTranslationPowers/NonsingularJetNorms/Taylor0ConstMul.lean#L195-L269
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/TorsionTranslationPowers/NonsingularJetNorms/Taylor0ConstMul.lean#L195-L269

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_StatementA
import Definitions.Def_Formalism_EllipticTorsion_FormalGroupPointsNoTorsion
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_FlowTwoTorsionWp
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_LogSigmaOnePullbackSpec
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_NonsingularJetNorms_Series
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_NonsingularJetNorms_Taylor0ConstMul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.E
open Formalism.L2.Th1.F (opU sgStar th0 taylor0)
open Formalism.L2.Th1.B (fExp fLog)
open Tor
open Classical

theorem Formalism.L2.Th1.E.Th0Analytic_of (hS : AnalyticSys) (hA : PtOfAdd) (hZ : PtOfZero) (hI : PtOfInt)
    (hU : TransUnit) (hG : TransGauss) (hO : OpUTh0Root) : ThetaZeroAnalytic := by sorry
