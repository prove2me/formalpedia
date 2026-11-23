-- Prove2me | Theorems.Thm_Formalism_L2_Th1_D_TorusDerivation_coeff_subst_scale
-- name    : Formalism.L2.Th1.D.TorusDerivation.coeff_subst_scale
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:14:33.046286+00:00
-- url     : https://prove2.me/theorems/d5b2a82d-104a-4131-9d54-4a54f66c7913
-- title:
--   Torus Derivation: coeff subst scale
-- statement:
--   The Torus Derivation construction uses the coeff subst scale property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/GaussSumParity/KummerThetaLogarithms/SubstZeroOfConstantCoeff.lean#L18-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/GaussSumParity/KummerThetaLogarithms/SubstZeroOfConstantCoeff.lean#L18-L27

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

theorem Formalism.L2.Th1.D.TorusDerivation.coeff_subst_scale {τ : Type} [Fintype τ] (a : τ → K) (f : MvPowerSeries τ K) (n : τ →₀ ℕ) :
    MvPowerSeries.coeff n
        (MvPowerSeries.subst (fun s => MvPowerSeries.C (a s) * MvPowerSeries.X s) f) =
      (∏ s, a s ^ n s) * MvPowerSeries.coeff n f := by sorry
