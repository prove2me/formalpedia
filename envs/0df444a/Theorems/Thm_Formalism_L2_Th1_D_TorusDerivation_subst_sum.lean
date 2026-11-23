-- Prove2me | Theorems.Thm_Formalism_L2_Th1_D_TorusDerivation_subst_sum
-- name    : Formalism.L2.Th1.D.TorusDerivation.subst_sum
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:14:59.568514+00:00
-- url     : https://prove2.me/theorems/af6b45be-d2a0-4a09-9a68-93ea62a58973
-- title:
--   Torus Derivation: subst sum
-- statement:
--   The Torus Derivation construction uses the subst sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/GaussSumParity/KummerThetaLogarithms/SubstZeroOfConstantCoeff.lean#L33-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/GaussSumParity/KummerThetaLogarithms/SubstZeroOfConstantCoeff.lean#L33-L36

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_LetterShift
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_BimultiplicativeDivisibleTorsion
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_SubstZeroOfConstantCoeff
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
open Formalism.DworkPowerSeriesWeights (torus lw degE degO NoLowBidegree)
open Formalism.InvariantFactorPaths.G7 (lgF at1 DivAB)
open Formalism.L2.Th1.D.TorusDerivation
variable {K : Type} [Field K]

theorem Formalism.L2.Th1.D.TorusDerivation.subst_sum {σ' τ α : Type} {a : σ' → MvPowerSeries τ K} (ha : MvPowerSeries.HasSubst a)
    (S : Finset α) (F : α → MvPowerSeries σ' K) :
    MvPowerSeries.subst a (∑ i ∈ S, F i) = ∑ i ∈ S, MvPowerSeries.subst a (F i) := by sorry
