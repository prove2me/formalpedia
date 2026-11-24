-- Prove2me | Theorems.Thm_Formalism_L2_Th1_D_B4_subst_first_odd
-- name    : Formalism.L2.Th1.D.B4.subst_first_odd
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T10:25:51.718322+00:00
-- url     : https://prove2.me/theorems/2def26fa-ef27-4bbc-ad1b-55c98931bee9
-- title:
--   B4: subst first odd
-- statement:
--   The B4 construction uses the subst first odd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/GaussSumParity/KummerThetaLogarithms/BiextensionHypothesesOfConditions.lean#L68-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/GaussSumParity/KummerThetaLogarithms/BiextensionHypothesesOfConditions.lean#L68-L71

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_LetterShift
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FinalS
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_Transfer
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_BiextensionHypothesesOfConditions
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
open Formalism.DworkPowerSeriesWeights (Integral mvExp torus BHyp NoLowBidegree letterLog de1 de2 s0 s1 s2 s1' s2' V2 degE)
open Formalism.InvariantFactorPaths.G7 (Simeq DivAB UnrOK IsLawOfLog)
open MvPowerSeries (subst HasSubst constantCoeff)
open Formalism.L2.Th1.D.B4
variable {K : Type} [Field K] {τ : Type} {d : ℕ} {a : V2 d → MvPowerSeries τ K}

theorem Formalism.L2.Th1.D.B4.subst_first_odd (ha : HasSubst a) {s : ZMod d} (hs : ¬ s.val % 2 = 0) :
    subst a (s1 (K := K) s) = a (false, s) := by sorry
