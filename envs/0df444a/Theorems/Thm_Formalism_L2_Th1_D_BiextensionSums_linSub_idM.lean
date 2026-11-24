-- Prove2me | Theorems.Thm_Formalism_L2_Th1_D_BiextensionSums_linSub_idM
-- name    : Formalism.L2.Th1.D.BiextensionSums.linSub_idM
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T11:04:38.299819+00:00
-- url     : https://prove2.me/theorems/73950c4d-96d0-4ed5-b1f6-8040abe8ecc6
-- title:
--   Biextension Sums: lin Sub id M
-- statement:
--   The Biextension Sums construction uses the lin Sub id M property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/GaussSumParity/KummerThetaLogarithms/BiextensionOfExpSpec.lean#L27-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/GaussSumParity/KummerThetaLogarithms/BiextensionOfExpSpec.lean#L27-L36

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

theorem Formalism.L2.Th1.D.BiextensionSums.linSub_idM {K : Type} [Field K] {d N0 N1 : ℕ} [NeZero d] :
    linSub (idM : ZV d N0 N1 → ZV d N0 N1 → K) = X := by sorry
