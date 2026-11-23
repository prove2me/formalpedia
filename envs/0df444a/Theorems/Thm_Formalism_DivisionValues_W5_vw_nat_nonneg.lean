-- Prove2me | Theorems.Thm_Formalism_DivisionValues_W5_vw_nat_nonneg
-- name    : Formalism.DivisionValues.W5.vw_nat_nonneg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:23:12.552794+00:00
-- url     : https://prove2.me/theorems/ac2b3d95-a12f-47c2-a9bd-37c8845d921b
-- title:
--   W5: vw nat nonneg
-- statement:
--   The W5 construction uses the vw nat nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/PlaceSumSquares.lean#L342-L345
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/PlaceSumSquares.lean#L342-L345

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_UntwistedChoice
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ConjugateWeightLatticeOfGeneral
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_PlaceSumSquares
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder
noncomputable section
open Formalism Formalism.DivisionValues
open Formalism.DivisionValues.W5
variable {K : Type} [Field K] [NumberField K]

theorem Formalism.DivisionValues.W5.vw_nat_nonneg (w : HeightOneSpectrum (𝓞 K)) (n : ℕ) : 0 ≤ vw w (n : K) := by sorry
