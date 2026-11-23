-- Prove2me | Theorems.Thm_Formalism_GradedWeylDivisibility_dualWeyl_pow
-- name    : Formalism.GradedWeylDivisibility.dualWeyl_pow
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:51:55.783903+00:00
-- url     : https://prove2.me/theorems/e56d9f29-7777-4798-b8f6-f1fab0613cc9
-- title:
--   Graded Weyl Divisibility: dual Weyl pow
-- statement:
--   The Graded Weyl Divisibility construction uses the dual Weyl pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/LBidetLemmas.lean#L32-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/LBidetLemmas.lean#L32-L37

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

theorem Formalism.GradedWeylDivisibility.dualWeyl_pow {R : Type*} [CommRing R] {r n : ℕ} {ν : Fin n → ℕ}
    {f : MvPolynomial (Fin r × Fin n) R} (hf : f ∈ dualWeyl R r n ν) (k : ℕ) :
    f ^ k ∈ dualWeyl R r n (k • ν) := by sorry
