-- Prove2me | Theorems.Thm_Formalism_L2_DIV_Test_mem_dual_one
-- name    : Formalism.L2.DIV.Test.mem_dual_one
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:49:27.749811+00:00
-- url     : https://prove2.me/theorems/54970729-201c-46a5-8281-bfa6a9293c55
-- title:
--   Test: mem dual one
-- statement:
--   The Test construction uses the mem dual one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/ProjLemmas.lean#L1449-L1469
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/ProjLemmas.lean#L1449-L1469

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

theorem Formalism.L2.DIV.Test.mem_dual_one (y : K) :
    y ∈ Formalism.HermitianLatticesTheory.dual (stdPair K) (1 : Submodule (𝓞 K) K) ↔ y ∈ (1 : Submodule (𝓞 K) K) := by sorry
