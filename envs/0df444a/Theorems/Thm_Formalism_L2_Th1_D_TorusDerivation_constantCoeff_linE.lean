-- Prove2me | Theorems.Thm_Formalism_L2_Th1_D_TorusDerivation_constantCoeff_linE
-- name    : Formalism.L2.Th1.D.TorusDerivation.constantCoeff_linE
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:16:15.287192+00:00
-- url     : https://prove2.me/theorems/01ea506a-5133-4087-a9d3-e7f77650daff
-- title:
--   Torus Derivation: constant Coeff lin E
-- statement:
--   The Torus Derivation construction uses the constant Coeff lin E property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/GaussSumParity/KummerThetaLogarithms/SubstZeroOfConstantCoeff.lean#L157-L162
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/GaussSumParity/KummerThetaLogarithms/SubstZeroOfConstantCoeff.lean#L157-L162

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
variable {d : ℕ} [NeZero d]

theorem Formalism.L2.Th1.D.TorusDerivation.constantCoeff_linE (σ : K →+* K) (c : K) :
    MvPowerSeries.constantCoeff (linE (d := d) σ c) = 0 := by sorry
