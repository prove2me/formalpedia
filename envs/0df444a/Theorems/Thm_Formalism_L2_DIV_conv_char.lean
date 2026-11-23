-- Prove2me | Theorems.Thm_Formalism_L2_DIV_conv_char
-- name    : Formalism.L2.DIV.conv_char
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T14:45:33.93879+00:00
-- url     : https://prove2.me/theorems/775dd8ba-90a5-4342-b92a-298377d6731d
-- title:
--   DIV: conv char
-- statement:
--   The DIV construction uses the conv char property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/ProjLemmas.lean#L854-L908
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/ProjLemmas.lean#L854-L908

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

theorem Formalism.L2.DIV.conv_char {χ χ' : G → K} (h : IsAbsIrrChar χ) (h' : IsAbsIrrChar χ') (u : G) :
    (∑ s, χ s⁻¹ * χ' (s * u)) * χ' 1 = if χ = χ' then (Fintype.card G : K) * χ' u else 0 := by sorry
