-- Prove2me | Theorems.Thm_Formalism_GradedWeylDivisibility_dualWeyl_prod
-- name    : Formalism.GradedWeylDivisibility.dualWeyl_prod
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T17:09:15.123302+00:00
-- url     : https://prove2.me/theorems/c0fd247a-4cf1-47b5-b4da-6e336e875255
-- title:
--   Graded Weyl Divisibility: dual Weyl prod
-- statement:
--   The Graded Weyl Divisibility construction uses the dual Weyl prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/LBidetLemmas.lean#L39-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/LBidetLemmas.lean#L39-L49

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

theorem Formalism.GradedWeylDivisibility.dualWeyl_prod {R : Type*} [CommRing R] {r n : ℕ} {ι : Type*} (s : Finset ι)
    (ν : ι → Fin n → ℕ) (f : ι → MvPolynomial (Fin r × Fin n) R)
    (hf : ∀ i ∈ s, f i ∈ dualWeyl R r n (ν i)) :
    (∏ i ∈ s, f i) ∈ dualWeyl R r n (∑ i ∈ s, ν i) := by sorry
