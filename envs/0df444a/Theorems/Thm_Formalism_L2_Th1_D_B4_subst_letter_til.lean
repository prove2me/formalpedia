-- Prove2me | Theorems.Thm_Formalism_L2_Th1_D_B4_subst_letter_til
-- name    : Formalism.L2.Th1.D.B4.subst_letter_til
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T10:25:37.646096+00:00
-- url     : https://prove2.me/theorems/f730d3a5-96f0-4fd6-ab92-a4fe24855ed4
-- title:
--   B4: subst letter til
-- statement:
--   The B4 construction uses the subst letter til property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/GaussSumParity/KummerThetaLogarithms/BiextensionHypothesesOfConditions.lean#L129-L141
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/GaussSumParity/KummerThetaLogarithms/BiextensionHypothesesOfConditions.lean#L129-L141

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

theorem Formalism.L2.Th1.D.B4.subst_letter_til (hS : SubstTil) {K : Type} [NormedField K] (l d : ℕ) [NeZero d]
    (σ : K →+* K) (hl : 2 ≤ l) (be0 : MvPowerSeries (Fin 2) K) (ι : Type) [Fintype ι]
    (om oms : ι → K) (S : ZMod d → MvPowerSeries (V2 d) K) (hS0 : ∀ s, constantCoeff (S s) = 0) :
    subst (letterLog (K := K) l) (subst S (beTil l σ be0 om oms)) =
      ∑ r, subst ![linEL σ (oms r) (fun s => subst (letterLog (K := K) l) (S s)),
        linOL σ (om r) (fun s => subst (letterLog (K := K) l) (S s))] (addC l be0) := by sorry
