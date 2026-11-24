-- Prove2me | Theorems.Thm_Formalism_L2_Th1_D_BiextensionSums_map_sumE
-- name    : Formalism.L2.Th1.D.BiextensionSums.map_sumE
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T11:05:13.926997+00:00
-- url     : https://prove2.me/theorems/0cf4e6c0-ef93-4c03-b453-e2ad6c4f45e6
-- title:
--   Biextension Sums: map sum E
-- statement:
--   The Biextension Sums construction uses the map sum E property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/GaussSumParity/KummerThetaLogarithms/BiextensionOfExpSpec.lean#L38-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/GaussSumParity/KummerThetaLogarithms/BiextensionOfExpSpec.lean#L38-L45

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_BiextensionPointsOfExpSpec
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_Transfer
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_BiextensionOfExpSpec
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_mvExp_add

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
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.D
open Formalism.DworkPowerSeriesWeights (Integral mvExp torus entLog thetaZ bSum linSub idM ZV)
open Formalism.InvariantFactorPaths.G7 (lgF at1 Simeq UnrOK IsLawOfLog mvExp_add)
open MvPowerSeries
open Pair
open Formalism.L2.Th1.D.BiextensionSums

theorem Formalism.L2.Th1.D.BiextensionSums.map_sumE {K0 K ι : Type} [Field K0] [Field K] [Fintype ι] {N0 N1 : ℕ} (j : K0 →+* K)
    (be : MvPowerSeries (Fin 2) K0) :
    map j (sumE (ι := ι) (N0 := N0) (N1 := N1) be) = sumE (map j be) := by sorry
