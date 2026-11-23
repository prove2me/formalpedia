-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_ExpSeriesBivariate_ExpSeriesAddition_CT_mul
-- name    : Formalism.HermitianLattices.ExpSeriesBivariate.ExpSeriesAddition.CT.mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:07:45.84567+00:00
-- url     : https://prove2.me/theorems/580f7690-5eae-4298-a433-9be4255a12a5
-- title:
--   CT: mul
-- statement:
--   The CT construction uses the mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/HookFormulaTorsion/ExpSeries.lean#L225-L232
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/HookFormulaTorsion/ExpSeries.lean#L225-L232

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

theorem Formalism.HermitianLattices.ExpSeriesBivariate.ExpSeriesAddition.CT.mul {F G : ℕ → MvPowerSeries σ K} {f g : MvPowerSeries σ K} (hF : CT F f)
    (hG : CT G g) : CT (fun k => F k * G k) (f * g) := by sorry
