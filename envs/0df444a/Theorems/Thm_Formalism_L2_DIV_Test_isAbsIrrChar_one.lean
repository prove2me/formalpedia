-- Prove2me | Theorems.Thm_Formalism_L2_DIV_Test_isAbsIrrChar_one
-- name    : Formalism.L2.DIV.Test.isAbsIrrChar_one
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:42:33.675184+00:00
-- url     : https://prove2.me/theorems/b04c75b6-97f7-4a23-a3ac-567136c1f664
-- title:
--   Test: is Abs Irr Char one
-- statement:
--   The Test construction uses the is Abs Irr Char one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/ProjLemmas.lean#L1372-L1386
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/ProjLemmas.lean#L1372-L1386

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
open Formalism Formalism.L2 Formalism.L2.DIV Formalism.L2.DIV.Test
open Formalism.DivisionValues
variable (K : Type) [Field K] [NumberField K] [StarRing K] (G : Type) [Group G] [Fintype G]

theorem Formalism.L2.DIV.Test.isAbsIrrChar_one : IsAbsIrrChar (fun _ : G => (1 : K)) := by sorry
