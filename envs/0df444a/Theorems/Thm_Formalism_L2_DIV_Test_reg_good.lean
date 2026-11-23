-- Prove2me | Theorems.Thm_Formalism_L2_DIV_Test_reg_good
-- name    : Formalism.L2.DIV.Test.reg_good
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T14:42:32.5353+00:00
-- url     : https://prove2.me/theorems/686684b7-9615-440e-84af-2b2eadf48708
-- title:
--   Test: reg good
-- statement:
--   The Test construction uses the reg good property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/ProjLemmas.lean#L1471-L1501
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/ProjLemmas.lean#L1471-L1501

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

theorem Formalism.L2.DIV.Test.reg_good : (regCSD K G).Good 1 := by sorry
