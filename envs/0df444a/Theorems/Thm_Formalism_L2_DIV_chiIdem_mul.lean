-- Prove2me | Theorems.Thm_Formalism_L2_DIV_chiIdem_mul
-- name    : Formalism.L2.DIV.chiIdem_mul
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:49:44.262794+00:00
-- url     : https://prove2.me/theorems/4610a727-8d0e-4d0b-a61b-c0895d6fca42
-- title:
--   DIV: chi Idem mul
-- statement:
--   The DIV construction uses the chi Idem mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/ProjLemmas.lean#L911-L934
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/ProjLemmas.lean#L911-L934

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_GoodPartHermitianSpec
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_ClassSumLemmas
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ClassSumDualGeOfFamily
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_ProjLemmas
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
open Formalism Formalism.L2 Formalism.L2.DIV
open Formalism.DivisionValues
open Representation
variable {K : Type} [Field K] [CharZero K] {G : Type} [Group G] [Fintype G]
open Classical

theorem Formalism.L2.DIV.chiIdem_mul {χ χ' : G → K} (h : IsAbsIrrChar χ) (h' : IsAbsIrrChar χ') :
    chiIdem χ * chiIdem χ' = if χ = χ' then chiIdem χ' else 0 := by sorry
