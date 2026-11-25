-- Prove2me | Theorems.Thm_Formalism_L2_Th1_D_BiextensionAlongSeries_integral_serAlong
-- name    : Formalism.L2.Th1.D.BiextensionAlongSeries.integral_serAlong
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T07:02:41.216733+00:00
-- url     : https://prove2.me/theorems/72c91759-5a5b-5a06-901b-800e5a759750
-- title:
--   Biextension Along Series: integral ser Along
-- statement:
--   The Biextension Along Series construction uses the integral ser Along property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/GaussSumParity/KummerThetaLogarithms/BiextensionRelationOfExpSpec.lean#L73-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/GaussSumParity/KummerThetaLogarithms/BiextensionRelationOfExpSpec.lean#L73-L76

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

theorem Formalism.L2.Th1.D.BiextensionAlongSeries.integral_serAlong [IsUltrametricDist K] {ι κ : Type} [Finite ι] (e : ι → κ)
    {f : MvPowerSeries ι K} (hf : Integral f) : Integral (serAlong e f) := by sorry
