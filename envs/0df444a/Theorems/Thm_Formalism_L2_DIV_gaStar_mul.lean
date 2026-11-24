-- Prove2me | Theorems.Thm_Formalism_L2_DIV_gaStar_mul
-- name    : Formalism.L2.DIV.gaStar_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:54:16.895851+00:00
-- url     : https://prove2.me/theorems/8f1dc320-f7e3-4cf7-a82a-7b35e0284ef4
-- title:
--   DIV: ga Star mul
-- statement:
--   The DIV construction uses the ga Star mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/ProjLemmas.lean#L385-L397
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/ProjLemmas.lean#L385-L397

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

theorem Formalism.L2.DIV.gaStar_mul [StarRing K] (a b : MonoidAlgebra K G) : gaStar (a * b) = gaStar b * gaStar a := by sorry
