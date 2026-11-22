-- Prove2me | Theorems.Thm_Formalism_DivisionValues_R0_map_inv_field
-- name    : Formalism.DivisionValues.R0.map_inv_field
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T18:39:29.194166+00:00
-- url     : https://prove2.me/theorems/8c00ba8b-ee80-47cf-8a68-8d8f1b66eebe
-- title:
--   R0: map inv field
-- statement:
--   The R0 construction uses the map inv field property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/ConjTransposeEqOfPosDef.lean#L15-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/ConjTransposeEqOfPosDef.lean#L15-L27

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

theorem Formalism.DivisionValues.R0.map_inv_field {F : Type} [Field F] (f : K →+* F) {ι : Type} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι K) : A⁻¹.map f = (A.map f)⁻¹ := by sorry
