-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_ExpSeriesBivariate_ExpSeriesAddition_exp_biv
-- name    : Formalism.HermitianLattices.ExpSeriesBivariate.ExpSeriesAddition.exp_biv
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:48:43.040682+00:00
-- url     : https://prove2.me/theorems/ca0e6e66-27b3-42f0-bb3a-2725b89cda76
-- title:
--   Exp Series Addition: exp biv
-- statement:
--   The Exp Series Addition construction uses the exp biv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/HookFormulaTorsion/ExpSeries.lean#L15-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/HookFormulaTorsion/ExpSeries.lean#L15-L32

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_LegendreCoefficient
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_IntegralSubstVector
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_ExpSeries
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.ExpSeriesBivariate Formalism.HermitianLattices.ExpSeriesBivariate.ExpSeriesAddition
open Finset Formalism.G Formalism.HermitianLattices.ExpSeriesBivariate
variable {σ K : Type} [Field K] [Algebra ℚ K]

theorem Formalism.HermitianLattices.ExpSeriesBivariate.ExpSeriesAddition.exp_biv :
    expS (MvPowerSeries.X 0 + MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) =
      expS (MvPowerSeries.X 0) * expS (MvPowerSeries.X 1) := by sorry
