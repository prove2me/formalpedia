-- Prove2me | Theorems.Thm_Formalism_L2_DIV_idemOf_mul_self
-- name    : Formalism.L2.DIV.idemOf_mul_self
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T14:40:46.046915+00:00
-- url     : https://prove2.me/theorems/7cb642a2-af08-465d-a8ae-bd534fbef404
-- title:
--   DIV: idem Of mul self
-- statement:
--   The DIV construction uses the idem Of mul self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/ProjLemmas.lean#L936-L943
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/ProjLemmas.lean#L936-L943

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

theorem Formalism.L2.DIV.idemOf_mul_self (X : Finset (G → K)) (hX : ∀ χ ∈ X, IsAbsIrrChar χ) :
    idemOf X * idemOf X = idemOf X := by sorry
