-- Prove2me | Theorems.Thm_Formalism_GradedWeylDivisibility_mem_dualWeyl_iff
-- name    : Formalism.GradedWeylDivisibility.mem_dualWeyl_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T17:09:06.237412+00:00
-- url     : https://prove2.me/theorems/d9f55551-4bfc-4a6b-93a0-5053c0826c53
-- title:
--   Graded Weyl Divisibility: mem dual Weyl iff
-- statement:
--   The Graded Weyl Divisibility construction uses the mem dual Weyl iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/LBidetLemmas.lean#L9-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/LBidetLemmas.lean#L9-L16

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

theorem Formalism.GradedWeylDivisibility.mem_dualWeyl_iff {R : Type*} [CommRing R] {r n : ℕ} {ν : Fin n → ℕ}
    {f : MvPolynomial (Fin r × Fin n) R} :
    f ∈ dualWeyl R r n ν ↔
      IsWeightedHomogeneous (colW r n) f ν ∧
        ∀ l j : Fin n, l < j → colAddGen R l j f = rename some f := by sorry
