-- Prove2me | Theorems.Thm_Formalism_L2_DIV_idemOf_central
-- name    : Formalism.L2.DIV.idemOf_central
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T14:40:54.169333+00:00
-- url     : https://prove2.me/theorems/453cb874-1dd0-4e79-b883-a1c92309e479
-- title:
--   DIV: idem Of central
-- statement:
--   The DIV construction uses the idem Of central property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/ProjLemmas.lean#L661-L667
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/ProjLemmas.lean#L661-L667

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

theorem Formalism.L2.DIV.idemOf_central (X : Finset (G → K)) (hX : ∀ χ ∈ X, IsAbsIrrChar χ) (b : MonoidAlgebra K G) :
    b * idemOf X = idemOf X * b := by sorry
