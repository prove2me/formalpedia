-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_ExpSeriesBivariate_ExpSeriesAddition_low_one
-- name    : Formalism.HermitianLattices.ExpSeriesBivariate.ExpSeriesAddition.low_one
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:44:02.993908+00:00
-- url     : https://prove2.me/theorems/2fcc47c4-c5be-4f57-9bcf-11d6178ac26f
-- title:
--   Exp Series Addition: low one
-- statement:
--   The Exp Series Addition construction uses the low one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/HookFormulaTorsion/ExpSeries.lean#L97-L107
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/HookFormulaTorsion/ExpSeries.lean#L97-L107

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

theorem Formalism.HermitianLattices.ExpSeriesBivariate.ExpSeriesAddition.low_one {x : MvPowerSeries σ K} (hx : MvPowerSeries.constantCoeff x = 0) : Low 1 x := by sorry
