-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_ExpSeriesBivariate_ExpSeriesAddition_subst_expS
-- name    : Formalism.HermitianLattices.ExpSeriesBivariate.ExpSeriesAddition.subst_expS
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:43:37.63604+00:00
-- url     : https://prove2.me/theorems/1d02b9a3-284d-4112-b330-57527604eadf
-- title:
--   Exp Series Addition: subst exp S
-- statement:
--   The Exp Series Addition construction uses the subst exp S property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/HookFormulaTorsion/ExpSeries.lean#L34-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/HookFormulaTorsion/ExpSeries.lean#L34-L42

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

theorem Formalism.HermitianLattices.ExpSeriesBivariate.ExpSeriesAddition.subst_expS {τ : Type} [Finite σ] (h : σ → MvPowerSeries τ K)
    (hh : ∀ i, MvPowerSeries.constantCoeff (h i) = 0) (f : MvPowerSeries σ K)
    (hf : MvPowerSeries.constantCoeff f = 0) :
    MvPowerSeries.subst h (expS f) = expS (MvPowerSeries.subst h f) := by sorry
