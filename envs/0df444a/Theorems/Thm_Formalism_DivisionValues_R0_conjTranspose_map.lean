-- Prove2me | Theorems.Thm_Formalism_DivisionValues_R0_conjTranspose_map
-- name    : Formalism.DivisionValues.R0.conjTranspose_map
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T00:01:09.319708+00:00
-- url     : https://prove2.me/theorems/d1d0c2a2-26c4-4b9f-94c1-4cd1651c4ddd
-- title:
--   R0: conj Transpose map
-- statement:
--   The R0 construction uses the conj Transpose map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/ConjTransposeEqOfPosDef.lean#L29-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/ConjTransposeEqOfPosDef.lean#L29-L33

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_ProdFormula
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ConjTransposeEqOfPosDef
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
open Formalism.DivisionValues.R0
variable {K : Type} [Field K] [StarRing K]

theorem Formalism.DivisionValues.R0.conjTranspose_map (σ : K →+* ℂ) (hσ : ∀ a : K, σ (star a) = starRingEnd ℂ (σ a))
    {m n : Type} (A : Matrix m n K) : Aᴴ.map σ = (A.map σ)ᴴ := by sorry
