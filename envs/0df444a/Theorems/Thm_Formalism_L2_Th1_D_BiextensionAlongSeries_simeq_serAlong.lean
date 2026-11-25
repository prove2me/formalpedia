-- Prove2me | Theorems.Thm_Formalism_L2_Th1_D_BiextensionAlongSeries_simeq_serAlong
-- name    : Formalism.L2.Th1.D.BiextensionAlongSeries.simeq_serAlong
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T07:21:16.978074+00:00
-- url     : https://prove2.me/theorems/1d7877e9-59c5-5da7-860c-b25868e69ef0
-- title:
--   Biextension Along Series: simeq ser Along
-- statement:
--   The Biextension Along Series construction uses the simeq ser Along property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/GaussSumParity/KummerThetaLogarithms/BiextensionRelationOfExpSpec.lean#L82-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/GaussSumParity/KummerThetaLogarithms/BiextensionRelationOfExpSpec.lean#L82-L85

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KurComplete
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_RelativeThetaFactorization
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_BiextensionOfExpSpec
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_BiextensionPointsOfExpSpec
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_BiextensionRelationOfExpSpec
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
open Formalism.DworkPowerSeriesWeights (Integral mvExp torus entLog bSum linSub idM ZV serAlong)
open Formalism.InvariantFactorPaths.G7 (lgF at1 Simeq UnrOK IsLawOfLog mvExp_add)
open MvPowerSeries
open Pair
open Formalism.L2.Th1.D.BiextensionAlongSeries
variable {K : Type} [NormedField K]

theorem Formalism.L2.Th1.D.BiextensionAlongSeries.simeq_serAlong [IsUltrametricDist K] [CharZero K] {ι κ : Type} [Finite ι] (e : ι → κ)
    {f g : MvPowerSeries ι K} (h : Simeq f g) : Simeq (serAlong e f) (serAlong e g) := by sorry
