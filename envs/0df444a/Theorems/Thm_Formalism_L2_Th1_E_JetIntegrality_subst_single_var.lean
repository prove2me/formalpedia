-- Prove2me | Theorems.Thm_Formalism_L2_Th1_E_JetIntegrality_subst_single_var
-- name    : Formalism.L2.Th1.E.JetIntegrality.subst_single_var
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T11:52:44.968176+00:00
-- url     : https://prove2.me/theorems/96310329-8a0b-5b56-ab0d-583179f0ca30
-- title:
--   Jet Integrality: subst single var
-- statement:
--   The Jet Integrality construction uses the subst single var property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/TorsionTranslationPowers/NonsingularJetNorms/JetsInOfOneVariable.lean#L21-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/TorsionTranslationPowers/NonsingularJetNorms/JetsInOfOneVariable.lean#L21-L30

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_PhNormFromDatum
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_NonsingularJetNorms_ConstantCoeffInVarEqZero
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_PairedSquareJets_Hurwitz
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_PairedSquareJets_HurwitzB
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_NonsingularJetNorms_JetsInOfOneVariable
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_FormalGroupLaws_subst_single_var
import Theorems.Thm_Formalism_L2_Th1_C_Clo_CoeffCont_subst

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.E
open Formalism.DworkPowerSeriesWeights (Integral mvExp mfact)
open Formalism.InvariantFactorPaths.G7 (at1)
open Formalism.L2.Th1.C (IsLogPair IsOneUnit jet)
open Formalism.L2.Th1.G (JetsIn JetsIn1)
open CompatibleChartOperations
open Formalism.L2.Th1.E.JetIntegrality
variable {K : Type} [Field K] {n : Type}

theorem Formalism.L2.Th1.E.JetIntegrality.subst_single_var [Finite n] {linv : PowerSeries K} (h0 : PowerSeries.constantCoeff linv = 0) (i : n)
    (g : PowerSeries K) :
    MvPowerSeries.subst (fun j : n => (at1 j linv : MvPowerSeries n K)) (at1 i g) =
      at1 i (PowerSeries.subst linv g) := by sorry
