-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_ExpSeriesBivariate_ExpSeriesAddition_coeff_expS
-- name    : Formalism.HermitianLattices.ExpSeriesBivariate.ExpSeriesAddition.coeff_expS
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T11:41:01.300219+00:00
-- url     : https://prove2.me/theorems/a9e44f01-76d7-466b-9c4a-74f32eb72ae6
-- title:
--   Exp Series Addition: coeff exp S
-- statement:
--   The Exp Series Addition construction uses the coeff exp S property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/HookFormulaTorsion/ExpSeries.lean#L115-L133
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/HookFormulaTorsion/ExpSeries.lean#L115-L133

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

theorem Formalism.HermitianLattices.ExpSeriesBivariate.ExpSeriesAddition.coeff_expS (f : MvPowerSeries σ K) (hf : MvPowerSeries.constantCoeff f = 0)
    (d : σ →₀ ℕ) (N : ℕ) (hN : d.degree < N) :
    MvPowerSeries.coeff d (expS f) =
      ∑ n ∈ range N, algebraMap ℚ K (1 / n.factorial) * MvPowerSeries.coeff d (f ^ n) := by sorry
