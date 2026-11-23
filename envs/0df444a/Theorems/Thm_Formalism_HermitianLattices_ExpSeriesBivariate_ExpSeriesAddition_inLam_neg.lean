-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_ExpSeriesBivariate_ExpSeriesAddition_inLam_neg
-- name    : Formalism.HermitianLattices.ExpSeriesBivariate.ExpSeriesAddition.inLam_neg
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T02:10:23.924321+00:00
-- url     : https://prove2.me/theorems/0b9c6837-1b18-4605-87d7-6a3aa75de90b
-- title:
--   Exp Series Addition: in Lam neg
-- statement:
--   The Exp Series Addition construction uses the in Lam neg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/HookFormulaTorsion/ExpSeries.lean#L265-L274
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/HookFormulaTorsion/ExpSeries.lean#L265-L274

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
variable {σ K : Type} [NormedField K]

theorem Formalism.HermitianLattices.ExpSeriesBivariate.ExpSeriesAddition.inLam_neg [IsUltrametricDist K] [Algebra ℚ K] {f : MvPowerSeries σ K} (hf : InLam f) :
    InLam (-f) := by sorry
