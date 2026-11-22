-- Prove2me | Theorems.Thm_Formalism_DivisionValues_star_mulVec_dot
-- name    : Formalism.DivisionValues.star_mulVec_dot
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T18:39:42.870809+00:00
-- url     : https://prove2.me/theorems/4ebf888c-a963-425b-a7a0-b0fea4661402
-- title:
--   Division Values: star mul Vec dot
-- statement:
--   The Division Values construction uses the star mul Vec dot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/SpecDet.lean#L21-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/SpecDet.lean#L21-L23

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_ProdFormula
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_SpecDet
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
variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem Formalism.DivisionValues.star_mulVec_dot {d : ℕ} (A N : Matrix (Fin d) (Fin d) ℂ) (u w : Fin d → ℂ) :
    star (A *ᵥ u) ⬝ᵥ (N *ᵥ (A *ᵥ w)) = star u ⬝ᵥ ((Aᴴ * N * A) *ᵥ w) := by sorry
