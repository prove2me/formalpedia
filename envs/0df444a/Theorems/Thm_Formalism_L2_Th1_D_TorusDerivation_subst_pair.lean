-- Prove2me | Theorems.Thm_Formalism_L2_Th1_D_TorusDerivation_subst_pair
-- name    : Formalism.L2.Th1.D.TorusDerivation.subst_pair
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:14:15.221791+00:00
-- url     : https://prove2.me/theorems/5d6fb252-7cb4-4824-9ca6-6df31932842c
-- title:
--   Torus Derivation: subst pair
-- statement:
--   The Torus Derivation construction uses the subst pair property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/GaussSumParity/KummerThetaLogarithms/SubstZeroOfConstantCoeff.lean#L51-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/GaussSumParity/KummerThetaLogarithms/SubstZeroOfConstantCoeff.lean#L51-L59

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

theorem Formalism.L2.Th1.D.TorusDerivation.subst_pair {τ κ : Type} {A B : MvPowerSeries τ K}
    (hA : MvPowerSeries.constantCoeff A = 0) (hB : MvPowerSeries.constantCoeff B = 0)
    {b : τ → MvPowerSeries κ K} (hb : MvPowerSeries.HasSubst b) (G : MvPowerSeries (Fin 2) K) :
    MvPowerSeries.subst b (MvPowerSeries.subst ![A, B] G) =
      MvPowerSeries.subst ![MvPowerSeries.subst b A, MvPowerSeries.subst b B] G := by sorry
