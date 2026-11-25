-- Prove2me | Theorems.Thm_Formalism_L2_Th1_E_GeneratorMatrix_coeff_tensor4
-- name    : Formalism.L2.Th1.E.GeneratorMatrix.coeff_tensor4
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T01:49:22.571928+00:00
-- url     : https://prove2.me/theorems/dd34bb41-7c56-5fa8-ad9e-6491683b8364
-- title:
--   Generator Matrix: coeff tensor4
-- statement:
--   The Generator Matrix construction uses the coeff tensor4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/TorsionTranslationPowers/NonsingularJetNorms/GeneralIntegrality.lean#L43-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/TorsionTranslationPowers/NonsingularJetNorms/GeneralIntegrality.lean#L43-L73

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_StatementN
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_NonsingularJetNorms_ConstantCoeffInVarEqZero
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_PhNormFromDatum
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_NonsingularJetNorms_GeneralIntegrality
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
open Formalism.DworkPowerSeriesWeights (Integral mvExp)
open Formalism.InvariantFactorPaths.G7 (at1 Simeq)
open Formalism.L2.Th1.C (IntMv IntPS IsPt IsLogPair)
open CompatibleChartOperations
open Formalism.L2.Th1.E.GeneratorMatrix
variable {K : Type} [Field K] {n : Type}

theorem Formalism.L2.Th1.E.GeneratorMatrix.coeff_tensor4 (f : MvPowerSeries n K) (ν : n →₀ ℕ) :
    MvPowerSeries.coeff (∑ a, Finsupp.embDomain (blk n a) ν) (tensor4 f) =
      MvPowerSeries.coeff ν f ^ 4 := by sorry
