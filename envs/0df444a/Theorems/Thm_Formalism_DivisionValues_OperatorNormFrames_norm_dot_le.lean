-- Prove2me | Theorems.Thm_Formalism_DivisionValues_OperatorNormFrames_norm_dot_le
-- name    : Formalism.DivisionValues.OperatorNormFrames.norm_dot_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:16:25.154729+00:00
-- url     : https://prove2.me/theorems/19b480d9-5545-4607-b0da-fb5919b69b4a
-- title:
--   Operator Norm Frames: norm dot le
-- statement:
--   The Operator Norm Frames construction uses the norm dot le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/DescendedNorm.lean#L27-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/DescendedNorm.lean#L27-L33

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_HeightBoundExactNorms
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ReductionThirdStepMean
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SlopeIneqMean
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_DescendedNorm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField
open scoped Matrix ComplexOrder InnerProductSpace
noncomputable section
open Formalism Formalism.DivisionValues
open Formalism.DivisionValues.OperatorNormFrames

theorem Formalism.DivisionValues.OperatorNormFrames.norm_dot_le {n : ℕ} (y w : Fin n → ℂ) :
    ‖y ⬝ᵥ w‖ ≤ Formalism.HermitianLatticesTheory.cnorm y * Formalism.HermitianLatticesTheory.cnorm w := by sorry
