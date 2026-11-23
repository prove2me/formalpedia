-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_ExpSeriesBivariate_ExpSeriesAddition_CT_pow
-- name    : Formalism.HermitianLattices.ExpSeriesBivariate.ExpSeriesAddition.CT.pow
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:03:16.231913+00:00
-- url     : https://prove2.me/theorems/c86a7d82-c7eb-476a-b8bf-0e1c3503e85d
-- title:
--   CT: pow
-- statement:
--   The CT construction uses the pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/HookFormulaTorsion/ExpSeries.lean#L234-L243
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/HookFormulaTorsion/ExpSeries.lean#L234-L243

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

theorem Formalism.HermitianLattices.ExpSeriesBivariate.ExpSeriesAddition.CT.pow {F : ℕ → MvPowerSeries σ K} {f : MvPowerSeries σ K} (hF : CT F f) (n : ℕ) :
    CT (fun k => F k ^ n) (f ^ n) := by sorry
