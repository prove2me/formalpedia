-- Prove2me | Theorems.Thm_Formalism_L2_Th1_E_GeneratorMatrix_blk_apply
-- name    : Formalism.L2.Th1.E.GeneratorMatrix.blk_apply
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T01:41:34.630802+00:00
-- url     : https://prove2.me/theorems/967a504a-8ab8-4234-a1ec-02c5de51f0fd
-- title:
--   Generator Matrix: blk apply
-- statement:
--   The Generator Matrix construction uses the blk apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/TorsionTranslationPowers/NonsingularJetNorms/GeneralIntegrality.lean#L19-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/TorsionTranslationPowers/NonsingularJetNorms/GeneralIntegrality.lean#L19-L26

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

theorem Formalism.L2.Th1.E.GeneratorMatrix.blk_apply {n : Type} (a b : Fin 4) (μ : n →₀ ℕ) (i : n) :
    Finsupp.embDomain (blk n a) μ (b, i) = if a = b then μ i else 0 := by sorry
