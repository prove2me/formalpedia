-- Prove2me | Theorems.Thm_Formalism_DivisionValues_single_dot_single
-- name    : Formalism.DivisionValues.single_dot_single
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T18:39:34.954434+00:00
-- url     : https://prove2.me/theorems/a22b4a05-f4a5-4c10-b30e-ecf07d6e2f25
-- title:
--   Division Values: single dot single
-- statement:
--   The Division Values construction uses the single dot single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/SpecDet.lean#L45-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/SpecDet.lean#L45-L53

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

theorem Formalism.DivisionValues.single_dot_single {d : ℕ} (N : Matrix (Fin d) (Fin d) ℂ) (a b : Fin d) :
    star (Pi.single a (1 : ℂ)) ⬝ᵥ (N *ᵥ Pi.single b (1 : ℂ)) = N a b := by sorry
