-- Prove2me | Theorems.Thm_Formalism_L2_Th1_D_B4_exp_of_simeq
-- name    : Formalism.L2.Th1.D.B4.exp_of_simeq
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T10:24:59.860392+00:00
-- url     : https://prove2.me/theorems/2e39e483-c510-4d52-8dc9-fdd1e3423c01
-- title:
--   B4: exp of simeq
-- statement:
--   The B4 construction uses the exp of simeq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/GaussSumParity/KummerThetaLogarithms/BiextensionHypothesesOfConditions.lean#L272-L284
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/GaussSumParity/KummerThetaLogarithms/BiextensionHypothesesOfConditions.lean#L272-L284

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
open B4
open Formalism.L2.Th1.D.B4

theorem Formalism.L2.Th1.D.B4.exp_of_simeq {K : Type} [NormedField K] [CharZero K] {d : ℕ} [NeZero d] (l : ℕ)
    {D : MvPowerSeries (V2 d) K} (h0 : constantCoeff D = 0)
    (h : Simeq (subst (letterLog (K := K) l) D) 0) :
    Integral (subst (letterLog (K := K) l) (mvExp D)) ∧
      constantCoeff (subst (letterLog (K := K) l) (mvExp D)) = 1 := by sorry
