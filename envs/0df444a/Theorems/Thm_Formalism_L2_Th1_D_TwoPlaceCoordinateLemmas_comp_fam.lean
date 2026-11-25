-- Prove2me | Theorems.Thm_Formalism_L2_Th1_D_TwoPlaceCoordinateLemmas_comp_fam
-- name    : Formalism.L2.Th1.D.TwoPlaceCoordinateLemmas.comp_fam
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T08:01:17.938898+00:00
-- url     : https://prove2.me/theorems/9c3b044a-1593-5762-9576-788eabe9e276
-- title:
--   Two Place Coordinate Lemmas: comp fam
-- statement:
--   The Two Place Coordinate Lemmas construction uses the comp fam property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/GaussSumParity/KummerThetaLogarithms/TwoPlaces.lean#L24-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/GaussSumParity/KummerThetaLogarithms/TwoPlaces.lean#L24-L31

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_TwoPlaces
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_SecondLevelOfNorm
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_BiextensionRelationOfExpSpec
import Definitions.Def_Formalism_GaussJetBounds_StatementW
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_TwoPlaces
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
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.D Formalism.L2.Th1.D.TwoPlaceCoordinateLemmas
open Formalism.DworkPowerSeriesWeights (Integral mvExp entLog bSum idM ZV serAlong HasJetBound OrbitsMul opAlong jetPairPoly)
open Formalism.InvariantFactorPaths.G7 (Simeq UnrOK IsLawOfLog)
open MvPowerSeries
open Formalism.L2.Th1.D Formalism.L2.Th1.D.BiextensionAlongSeries

theorem Formalism.L2.Th1.D.TwoPlaceCoordinateLemmas.comp_fam {K : Type} [Field K] {α β γ : Type} {A : α → MvPowerSeries β K}
    {C : β → MvPowerSeries γ K} (hA : HasSubst A) (hC : HasSubst C) (f : MvPowerSeries α K)
    (T : α → MvPowerSeries γ K) (hT : ∀ x, subst C (A x) = T x) :
    subst C (subst A f) = subst T f := by sorry
