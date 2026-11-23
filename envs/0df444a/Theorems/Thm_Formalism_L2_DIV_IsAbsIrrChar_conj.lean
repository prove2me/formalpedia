-- Prove2me | Theorems.Thm_Formalism_L2_DIV_IsAbsIrrChar_conj
-- name    : Formalism.L2.DIV.IsAbsIrrChar.conj
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:40:34.80166+00:00
-- url     : https://prove2.me/theorems/dc9233e7-7b71-45bc-83e1-06db374274e8
-- title:
--   Is Abs Irr Char: conj
-- statement:
--   The Is Abs Irr Char construction uses the conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/ProjLemmas.lean#L606-L612
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/ProjLemmas.lean#L606-L612

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
variable {K : Type} [Field K] {G : Type} [Group G] [Fintype G]

theorem Formalism.L2.DIV.IsAbsIrrChar.conj {χ : G → K} (h : IsAbsIrrChar χ) (s t : G) : χ (s * t * s⁻¹) = χ t := by sorry
