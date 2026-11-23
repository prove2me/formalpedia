-- Prove2me | Theorems.Thm_Formalism_L2_Th1_D_TorusDerivation_subst_scale_linE
-- name    : Formalism.L2.Th1.D.TorusDerivation.subst_scale_linE
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:16:18.857914+00:00
-- url     : https://prove2.me/theorems/02e6fc51-964c-4e4d-aa03-6d691304d28f
-- title:
--   Torus Derivation: subst scale lin E
-- statement:
--   The Torus Derivation construction uses the subst scale lin E property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/GaussSumParity/KummerThetaLogarithms/SubstZeroOfConstantCoeff.lean#L171-L181
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/GaussSumParity/KummerThetaLogarithms/SubstZeroOfConstantCoeff.lean#L171-L181

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

theorem Formalism.L2.Th1.D.TorusDerivation.subst_scale_linE (σ : K →+* K) (c : K) (a : ZMod d → K) :
    MvPowerSeries.subst (fun s => MvPowerSeries.C (a s) * MvPowerSeries.X s) (linE (d := d) σ c) =
      ∑ s : ZMod d, if s.val % 2 = 0 then MvPowerSeries.C (σ^[s.val] c * a s) * MvPowerSeries.X s
        else 0 := by sorry
