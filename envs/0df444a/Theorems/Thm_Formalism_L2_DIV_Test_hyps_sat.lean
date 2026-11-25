-- Prove2me | Theorems.Thm_Formalism_L2_DIV_Test_hyps_sat
-- name    : Formalism.L2.DIV.Test.hyps_sat
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T11:45:55.285106+00:00
-- url     : https://prove2.me/theorems/57a04d8d-6db2-40fc-88f8-3a5289131cd2
-- title:
--   Test: hyps sat
-- statement:
--   The Test construction uses the hyps sat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/ProjLemmas.lean#L1576-L1589
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/ProjLemmas.lean#L1576-L1589

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

theorem Formalism.L2.DIV.Test.hyps_sat (P : Subgroup (Equiv.Perm (Fin 3))) :
    ∃ v0 : InfinitePlace ℚ, IsConjAt v0 ∧
      (regCSD ℚ (Equiv.Perm (Fin 3))).Good 1 ∧
      ((regCSD ℚ (Equiv.Perm (Fin 3))).H.map v0.embedding).PosDef ∧
      (regCSD ℚ (Equiv.Perm (Fin 3))).ActGood (regAct ℚ (Equiv.Perm (Fin 3))) ∧
      (∀ χ ∈ ({fun _ => (1 : ℚ)} : Finset (Equiv.Perm (Fin 3) → ℚ)), IsAbsIrrChar χ) ∧
      0 < (regCSD ℚ (Equiv.Perm (Fin 3))).BaseDimension (regAct ℚ (Equiv.Perm (Fin 3)))
        ({fun _ => (1 : ℚ)} : Finset (Equiv.Perm (Fin 3) → ℚ)) P 1 := by sorry
