-- Prove2me | Theorems.Thm_Formalism_L2_Th1_D_TorusDerivation_subst_scale_linO
-- name    : Formalism.L2.Th1.D.TorusDerivation.subst_scale_linO
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:16:15.813936+00:00
-- url     : https://prove2.me/theorems/bbf62ba6-60ce-4c02-b8be-fee12a99fdab
-- title:
--   Torus Derivation: subst scale lin O
-- statement:
--   The Torus Derivation construction uses the subst scale lin O property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/GaussSumParity/KummerThetaLogarithms/SubstZeroOfConstantCoeff.lean#L183-L193
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/GaussSumParity/KummerThetaLogarithms/SubstZeroOfConstantCoeff.lean#L183-L193

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

theorem Formalism.L2.Th1.D.TorusDerivation.subst_scale_linO (σ : K →+* K) (c : K) (a : ZMod d → K) :
    MvPowerSeries.subst (fun s => MvPowerSeries.C (a s) * MvPowerSeries.X s) (linO (d := d) σ c) =
      ∑ s : ZMod d, if s.val % 2 = 0 then 0
        else MvPowerSeries.C (σ^[s.val] c * a s) * MvPowerSeries.X s := by sorry
