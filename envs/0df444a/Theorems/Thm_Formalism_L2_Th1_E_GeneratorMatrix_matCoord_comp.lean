-- Prove2me | Theorems.Thm_Formalism_L2_Th1_E_GeneratorMatrix_matCoord_comp
-- name    : Formalism.L2.Th1.E.GeneratorMatrix.matCoord_comp
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T01:51:12.337807+00:00
-- url     : https://prove2.me/theorems/204a1253-3eb3-4c73-85ba-4359352b00ef
-- title:
--   Generator Matrix: mat Coord comp
-- statement:
--   The Generator Matrix construction uses the mat Coord comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/TorsionTranslationPowers/NonsingularJetNorms/GeneralIntegrality.lean#L85-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/TorsionTranslationPowers/NonsingularJetNorms/GeneralIntegrality.lean#L85-L112

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_StatementN
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_NonsingularJetNorms_ConstantCoeffInVarEqZero
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_PhNormFromDatum
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_NonsingularJetNorms_GeneralIntegrality
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
open Formalism.DworkPowerSeriesWeights (Integral mvExp)
open Formalism.InvariantFactorPaths.G7 (at1 Simeq)
open Formalism.L2.Th1.C (IntMv IntPS IsPt IsLogPair)
open CompatibleChartOperations
open Formalism.L2.Th1.E.GeneratorMatrix
variable {K : Type} [Field K] {O m : Type} [CommRing O] [Fintype m] {l linv : PowerSeries K}

theorem Formalism.L2.Th1.E.GeneratorMatrix.matCoord_comp (h : IsLogPair l linv) (τ : O →+* K) (γ δ : Matrix m m O) (w : m) :
    MvPowerSeries.subst (matCoord l linv τ δ) (matCoord l linv τ γ w) =
      matCoord l linv τ (γ * δ) w := by sorry
