-- Prove2me | Theorems.Thm_Formalism_L2_DIV_subE_mulVec
-- name    : Formalism.L2.DIV.subE_mulVec
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:41:22.547971+00:00
-- url     : https://prove2.me/theorems/6e227c71-9c56-4c47-933a-632711b9487d
-- title:
--   DIV: sub E mul Vec
-- statement:
--   The DIV construction uses the sub E mul Vec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/ProjLemmas.lean#L19-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/ProjLemmas.lean#L19-L24

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
variable {K : Type} [Field K] [StarRing K] {n : ℕ}

theorem Formalism.L2.DIV.subE_mulVec (Z : Submodule K (Fin n → K)) (x : Fin (subDim Z) → K) :
    (subE Z).mulVec x = (((subBasis Z).equivFun.symm x : Z) : Fin n → K) := by sorry
