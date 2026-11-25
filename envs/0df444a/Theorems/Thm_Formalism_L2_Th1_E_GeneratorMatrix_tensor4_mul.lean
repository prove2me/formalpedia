-- Prove2me | Theorems.Thm_Formalism_L2_Th1_E_GeneratorMatrix_tensor4_mul
-- name    : Formalism.L2.Th1.E.GeneratorMatrix.tensor4_mul
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T01:51:53.450132+00:00
-- url     : https://prove2.me/theorems/92e738de-cb70-458d-8798-e29d99be22d4
-- title:
--   Generator Matrix: tensor4 mul
-- statement:
--   The Generator Matrix construction uses the tensor4 mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/TorsionTranslationPowers/NonsingularJetNorms/GeneralIntegrality.lean#L39-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/TorsionTranslationPowers/NonsingularJetNorms/GeneralIntegrality.lean#L39-L41

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

theorem Formalism.L2.Th1.E.GeneratorMatrix.tensor4_mul (f g : MvPowerSeries n K) : tensor4 (f * g) = tensor4 f * tensor4 g := by sorry
