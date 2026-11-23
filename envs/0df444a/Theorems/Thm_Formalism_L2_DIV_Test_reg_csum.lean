-- Prove2me | Theorems.Thm_Formalism_L2_DIV_Test_reg_csum
-- name    : Formalism.L2.DIV.Test.reg_csum
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T14:42:58.305019+00:00
-- url     : https://prove2.me/theorems/9ed4b7c2-bcc1-4e23-83a2-0334ad3f9418
-- title:
--   Test: reg csum
-- statement:
--   The Test construction uses the reg csum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/ProjLemmas.lean#L1355-L1358
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/ProjLemmas.lean#L1355-L1358

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

theorem Formalism.L2.DIV.Test.reg_csum (f g : G → K) : (regCSD K G).csum f g = ∑ c : G, star (f c) * g c := by sorry
