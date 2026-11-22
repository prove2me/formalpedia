-- Prove2me | Theorems.Thm_Formalism_GradedWeylDivisibility_dualWeyl_of_eq
-- name    : Formalism.GradedWeylDivisibility.dualWeyl_of_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T17:08:59.430802+00:00
-- url     : https://prove2.me/theorems/4b348951-8774-4b62-b555-7d1eae3f1636
-- title:
--   Graded Weyl Divisibility: dual Weyl of eq
-- statement:
--   The Graded Weyl Divisibility construction uses the dual Weyl of eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/LBidetLemmas.lean#L51-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/LBidetLemmas.lean#L51-L53

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

theorem Formalism.GradedWeylDivisibility.dualWeyl_of_eq {R : Type*} [CommRing R] {r n : ℕ} {ν μ : Fin n → ℕ}
    {f : MvPolynomial (Fin r × Fin n) R} (hf : f ∈ dualWeyl R r n ν) (h : ν = μ) :
    f ∈ dualWeyl R r n μ := by sorry
