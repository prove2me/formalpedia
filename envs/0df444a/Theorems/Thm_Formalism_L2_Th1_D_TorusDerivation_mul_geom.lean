-- Prove2me | Theorems.Thm_Formalism_L2_Th1_D_TorusDerivation_mul_geom
-- name    : Formalism.L2.Th1.D.TorusDerivation.mul_geom
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T09:10:34.795737+00:00
-- url     : https://prove2.me/theorems/29e47dde-f522-474b-928c-f45f6ecd3e92
-- title:
--   Torus Derivation: mul geom
-- statement:
--   The Torus Derivation construction uses the mul geom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/GaussSumParity/KummerThetaLogarithms/SubstZeroOfConstantCoeff.lean#L274-L281
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/GaussSumParity/KummerThetaLogarithms/SubstZeroOfConstantCoeff.lean#L274-L281

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
open TorusDerivation
open Formalism.L2.Th1.D.TorusDerivation
variable {K : Type} [Field K] {d : ℕ} [NeZero d]

theorem Formalism.L2.Th1.D.TorusDerivation.mul_geom {w : K} {N : ℕ} (h : w ^ N = 1) :
    w * ∑ k ∈ Finset.range N, w ^ k = ∑ k ∈ Finset.range N, w ^ k := by sorry
