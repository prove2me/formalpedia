-- Prove2me | Theorems.Thm_Formalism_L2_DIV_exists_mul_of_range_le
-- name    : Formalism.L2.DIV.exists_mul_of_range_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:42:55.660006+00:00
-- url     : https://prove2.me/theorems/bb3a73f1-c39d-4fe1-ad14-3670f623cf00
-- title:
--   DIV: exists mul of range le
-- statement:
--   The DIV construction uses the exists mul of range le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/ProjLemmas.lean#L1116-L1120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/ProjLemmas.lean#L1116-L1120

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

theorem Formalism.L2.DIV.exists_mul_of_range_le {K : Type} [Field K] {m n p : ℕ} {A : Matrix (Fin m) (Fin n) K}
    {B : Matrix (Fin m) (Fin p) K}
    (h : LinearMap.range B.mulVecLin ≤ LinearMap.range A.mulVecLin) :
    ∃ C : Matrix (Fin n) (Fin p) K, B = A * C := by sorry
