-- Prove2me | Theorems.Thm_Formalism_L2_Th1_D_TorusDerivation_coeff_pair_degE
-- name    : Formalism.L2.Th1.D.TorusDerivation.coeff_pair_degE
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:56:44.361804+00:00
-- url     : https://prove2.me/theorems/0b136ecf-96ba-4a43-8cea-374c0ecba8b0
-- title:
--   Torus Derivation: coeff pair deg E
-- statement:
--   The Torus Derivation construction uses the coeff pair deg E property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/GaussSumParity/KummerThetaLogarithms/SubstZeroOfConstantCoeff.lean#L320-L349
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/GaussSumParity/KummerThetaLogarithms/SubstZeroOfConstantCoeff.lean#L320-L349

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

theorem Formalism.L2.Th1.D.TorusDerivation.coeff_pair_degE {G : MvPowerSeries (Fin 2) K} (hG : DivAB G) (σ : K →+* K) (c c' : K)
    {n : ZMod d →₀ ℕ} (hn : degE n = 0) :
    MvPowerSeries.coeff n (MvPowerSeries.subst ![linE σ c, linO σ c'] G) = 0 := by sorry
