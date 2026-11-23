-- Prove2me | Theorems.Thm_Formalism_L2_Th1_D_TorusDerivation_coeff_beMean
-- name    : Formalism.L2.Th1.D.TorusDerivation.coeff_beMean
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T04:24:31.925463+00:00
-- url     : https://prove2.me/theorems/3545f2d8-7fa5-4a14-bf7a-6e6f05751697
-- title:
--   Torus Derivation: coeff be Mean
-- statement:
--   The Torus Derivation construction uses the coeff be Mean property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/GaussSumParity/KummerThetaLogarithms/SubstZeroOfConstantCoeff.lean#L248-L264
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/GaussSumParity/KummerThetaLogarithms/SubstZeroOfConstantCoeff.lean#L248-L264

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

theorem Formalism.L2.Th1.D.TorusDerivation.coeff_beMean {ι : Type} [Fintype ι] (l : ℕ) (σ : K →+* K) (be0 : MvPowerSeries (Fin 2) K)
    (om oms : ι → K) (ζ : K) (n : ZMod d →₀ ℕ) :
    MvPowerSeries.coeff n (beMean l σ be0 om oms ζ) =
      (((l ^ d - 1 : ℕ) : K)⁻¹) * ((∑ k ∈ Finset.range (l ^ d - 1), wt l ζ n ^ k) *
        MvPowerSeries.coeff n (beTil l σ be0 om oms)) := by sorry
