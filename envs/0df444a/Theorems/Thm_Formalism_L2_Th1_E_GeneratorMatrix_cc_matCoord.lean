-- Prove2me | Theorems.Thm_Formalism_L2_Th1_E_GeneratorMatrix_cc_matCoord
-- name    : Formalism.L2.Th1.E.GeneratorMatrix.cc_matCoord
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T01:40:32.646087+00:00
-- url     : https://prove2.me/theorems/800745c7-1d77-526a-8278-2f0a8d17510b
-- title:
--   Generator Matrix: cc mat Coord
-- statement:
--   The Generator Matrix construction uses the cc mat Coord property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/TorsionTranslationPowers/NonsingularJetNorms/GeneralIntegrality.lean#L81-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/TorsionTranslationPowers/NonsingularJetNorms/GeneralIntegrality.lean#L81-L83

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
variable {K : Type} [Field K] {O m : Type} [CommRing O] [Fintype m] {l linv : PowerSeries K}

theorem Formalism.L2.Th1.E.GeneratorMatrix.cc_matCoord (h : IsLogPair l linv) (τ : O →+* K) (γ : Matrix m m O) (w : m) :
    MvPowerSeries.constantCoeff (matCoord l linv τ γ w) = 0 := by sorry
