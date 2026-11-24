-- Prove2me | Theorems.Thm_Formalism_L2_Th1_D_TorusDerivation_wt_ne_one
-- name    : Formalism.L2.Th1.D.TorusDerivation.wt_ne_one
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T09:01:07.301611+00:00
-- url     : https://prove2.me/theorems/8cb2170e-1c40-44c7-99dc-9ceef47918ed
-- title:
--   Torus Derivation: wt ne one
-- statement:
--   The Torus Derivation construction uses the wt ne one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/GaussSumParity/KummerThetaLogarithms/SubstZeroOfConstantCoeff.lean#L365-L410
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/GaussSumParity/KummerThetaLogarithms/SubstZeroOfConstantCoeff.lean#L365-L410

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

theorem Formalism.L2.Th1.D.TorusDerivation.wt_ne_one {l : ℕ} (hl : 2 ≤ l) {ζ : K} (hζ : IsPrimitiveRoot ζ (l ^ d - 1))
    {n : ZMod d →₀ ℕ} (hE : degE n = 1) (hO : degO n = 1) : wt l ζ n ≠ 1 := by sorry
