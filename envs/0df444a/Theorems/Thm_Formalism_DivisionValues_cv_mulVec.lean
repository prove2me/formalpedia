-- Prove2me | Theorems.Thm_Formalism_DivisionValues_cv_mulVec
-- name    : Formalism.DivisionValues.cv_mulVec
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T00:05:15.362385+00:00
-- url     : https://prove2.me/theorems/d1e05832-3dfa-473a-ae28-8ba7010f89c0
-- title:
--   Division Values: cv mul Vec
-- statement:
--   The Division Values construction uses the cv mul Vec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/SpecDet.lean#L33-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/SpecDet.lean#L33-L36

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

theorem Formalism.DivisionValues.cv_mulVec {d : ℕ} (σ : K →+* ℂ) (φ : Matrix (Fin d) (Fin d) K) (x : Fin d → K) :
    cv σ (φ *ᵥ x) = (φ.map σ) *ᵥ cv σ x := by sorry
