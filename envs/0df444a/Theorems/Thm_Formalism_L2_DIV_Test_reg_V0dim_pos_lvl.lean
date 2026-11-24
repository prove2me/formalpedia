-- Prove2me | Theorems.Thm_Formalism_L2_DIV_Test_reg_V0dim_pos_lvl
-- name    : Formalism.L2.DIV.Test.reg_V0dim_pos_lvl
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:41:40.784284+00:00
-- url     : https://prove2.me/theorems/2b017e07-7751-4cab-97ac-99f3731e5872
-- title:
--   Test: reg V0dim pos lvl
-- statement:
--   The Test construction uses the reg V0dim pos lvl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/ProjLemmas.lean#L1564-L1570
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/ProjLemmas.lean#L1564-L1570

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

theorem Formalism.L2.DIV.Test.reg_V0dim_pos_lvl (P : Subgroup G) :
    0 < (regCSD K G).BaseDimension (regAct K G) ({fun _ : G => (1 : K)} : Finset (G → K)) P 1 := by sorry
