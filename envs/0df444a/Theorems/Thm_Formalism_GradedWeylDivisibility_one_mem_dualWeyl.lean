-- Prove2me | Theorems.Thm_Formalism_GradedWeylDivisibility_one_mem_dualWeyl
-- name    : Formalism.GradedWeylDivisibility.one_mem_dualWeyl
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T17:00:09.865526+00:00
-- url     : https://prove2.me/theorems/39036d44-9a06-4bcc-a8ef-991d39bd1ec1
-- title:
--   Graded Weyl Divisibility: one mem dual Weyl
-- statement:
--   The Graded Weyl Divisibility construction uses the one mem dual Weyl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/LBidetLemmas.lean#L26-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/LBidetLemmas.lean#L26-L30

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementA
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LBidetLemmas
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.GradedWeylDivisibility

theorem Formalism.GradedWeylDivisibility.one_mem_dualWeyl {R : Type*} [CommRing R] {r n : ℕ} :
    (1 : MvPolynomial (Fin r × Fin n) R) ∈ dualWeyl R r n 0 := by sorry
