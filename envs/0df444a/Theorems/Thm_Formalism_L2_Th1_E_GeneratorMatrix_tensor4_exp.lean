-- Prove2me | Theorems.Thm_Formalism_L2_Th1_E_GeneratorMatrix_tensor4_exp
-- name    : Formalism.L2.Th1.E.GeneratorMatrix.tensor4_exp
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T01:40:28.240448+00:00
-- url     : https://prove2.me/theorems/b225be1a-b9c6-4d95-a69e-ac2161a44d5b
-- title:
--   Generator Matrix: tensor4 exp
-- statement:
--   The Generator Matrix construction uses the tensor4 exp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/TorsionTranslationPowers/NonsingularJetNorms/GeneralIntegrality.lean#L130-L152
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/TorsionTranslationPowers/NonsingularJetNorms/GeneralIntegrality.lean#L130-L152

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
variable {K : Type} [NormedField K] [CharZero K] {n : Type} [Fintype n]

theorem Formalism.L2.Th1.E.GeneratorMatrix.tensor4_exp {ph : PowerSeries K} (hph : PowerSeries.constantCoeff ph = 0) :
    tensor4 (mvExp (phSum ph : MvPowerSeries n K)) =
      mvExp (phSum ph : MvPowerSeries (Fin 4 × n) K) := by sorry
