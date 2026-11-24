-- Prove2me | Theorems.Thm_Formalism_L2_Th1_D_TorusDerivation_divAB_of_axes
-- name    : Formalism.L2.Th1.D.TorusDerivation.divAB_of_axes
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T09:10:40.420828+00:00
-- url     : https://prove2.me/theorems/3319e91f-973f-4e83-9094-f65440b492af
-- title:
--   Torus Derivation: div AB of axes
-- statement:
--   The Torus Derivation construction uses the div AB of axes property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/GaussSumParity/KummerThetaLogarithms/SubstZeroOfConstantCoeff.lean#L83-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/GaussSumParity/KummerThetaLogarithms/SubstZeroOfConstantCoeff.lean#L83-L102

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

theorem Formalism.L2.Th1.D.TorusDerivation.divAB_of_axes {H : MvPowerSeries (Fin 2) K}
    (h1 : MvPowerSeries.subst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K), 0] H = 0)
    (h0 : MvPowerSeries.subst ![(0 : MvPowerSeries (Fin 2) K), MvPowerSeries.X 1] H = 0) :
    DivAB H := by sorry
