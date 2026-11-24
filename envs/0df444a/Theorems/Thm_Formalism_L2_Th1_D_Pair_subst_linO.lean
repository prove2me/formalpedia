-- Prove2me | Theorems.Thm_Formalism_L2_Th1_D_Pair_subst_linO
-- name    : Formalism.L2.Th1.D.Pair.subst_linO
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T10:23:28.304806+00:00
-- url     : https://prove2.me/theorems/3d90ab7b-111a-4496-ad92-6384b5416af3
-- title:
--   Pair: subst lin O
-- statement:
--   The Pair construction uses the subst lin O property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/GaussSumParity/KummerThetaLogarithms/SubstFirstCoboundaryThree.lean#L253-L259
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/GaussSumParity/KummerThetaLogarithms/SubstFirstCoboundaryThree.lean#L253-L259

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_LetterShift
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FinalS
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_SubstFirstCoboundaryThree
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
open Formalism.DworkPowerSeriesWeights (Integral mvExp)
open Formalism.InvariantFactorPaths.G7 (lgF at1 Simeq DivAB d1 swap2 in3 cob UnrOK IsLawOfLog SimeqRules)
open MvPowerSeries
open Formalism.L2.Th1.D.Pair
variable {K : Type} [NormedField K]

theorem Formalism.L2.Th1.D.Pair.subst_linO {d : ℕ} [NeZero d] (σ : K →+* K) (c : K) {τ : Type}
    {L : ZMod d → MvPowerSeries τ K} (hL : HasSubst L) :
    subst L (linO σ c) = linOL σ c L := by sorry
