-- Prove2me | Theorems.Thm_Formalism_L2_Th1_D_ChainWitness_fieldWitness
-- name    : Formalism.L2.Th1.D.ChainWitness.fieldWitness
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T07:21:09.392905+00:00
-- url     : https://prove2.me/theorems/006dc4b5-f985-559b-a837-0a81ce9ca015
-- title:
--   Chain Witness: field Witness
-- statement:
--   The Chain Witness construction uses the field Witness property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/GaussSumParity/KummerThetaLogarithms/NonVac.lean#L16-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/GaussSumParity/KummerThetaLogarithms/NonVac.lean#L16-L53

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_StatementN
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KurComplete
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_KernelFromKOne
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FinalS
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_NonVac
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
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.D Formalism.L2.Th1.D.ChainWitness
open Formalism.L2.Th1.D
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.DworkPowerSeriesWeights (Integral Unram)
open Formalism.InvariantFactorPaths.G7 (UnrOK IsLawOfLog Simeq Gser BetaHyp)

theorem Formalism.L2.Th1.D.ChainWitness.fieldWitness (hF : KurFrob) (hR : KurRoots) (hC : KurComplete) (hT : TrDualExists)
    (hB : FOfBetaHyp) (l : ℕ) [Fact l.Prime] (hl : 2 < l) (ν : ℕ) [NeZero ν] :
    ∃ σ : MaximalUnramifiedExtension l →+* MaximalUnramifiedExtension l, UnrOK (MaximalUnramifiedExtension l) l σ ∧ CompleteSpace (MaximalUnramifiedExtension l) ∧
      (∀ a, ‖(MaximalUnramifiedExtension l).subtype a‖ = ‖a‖) ∧
      (∃ ζ : MaximalUnramifiedExtension l, IsPrimitiveRoot ζ (l ^ 2 - 1)) ∧
      (∃ ζ : MaximalUnramifiedExtension l, IsPrimitiveRoot ζ (l ^ (2 * ν) - 1)) ∧
      2 ≤ 2 * ν ∧ Even (2 * ν) ∧
      (∃ ϖ : ℂ_[l], ϖ ^ (l ^ 2 - 1) = (l : ℂ_[l])) ∧
      (∃ om oms : Fin ν → MaximalUnramifiedExtension l, OwOK (2 * ν) σ om oms ∧ TrDual (2 * ν) σ om oms) ∧
      ∃ F : MvPowerSeries (Fin 2) (MaximalUnramifiedExtension l), IsLawOfLog l F ∧
        ∃ be : MvPowerSeries (Fin 2) (MaximalUnramifiedExtension l), F1 F be ∧ F2 l σ be ∧ ¬ Simeq be 0 := by sorry
