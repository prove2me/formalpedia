-- Prove2me | Theorems.Thm_Formalism_GradedWeylDivisibility_lehw_dom
-- name    : Formalism.GradedWeylDivisibility.lehw_dom
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:07:08.239023+00:00
-- url     : https://prove2.me/theorems/fab86d32-073f-4f20-9444-4817e0e5f50e
-- title:
--   Graded Weyl Divisibility: lehw dom
-- statement:
--   The Graded Weyl Divisibility construction uses the lehw dom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/LEhwLemmas.lean#L12-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/LEhwLemmas.lean#L12-L46

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementE
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LHwlineLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LHwrowLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_DualWeylDominanceOf
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LEhwLemmas
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

theorem Formalism.GradedWeylDivisibility.lehw_dom {r n : ℕ} (ν : Fin n → ℕ) (hnr : n ≤ r) (hν : Antitone ν)
    (f : MvPolynomial (Fin r × Fin n) ℚ) (hf : f ∈ dualWeyl ℚ r n ν) :
    ∀ m ∈ f.support, ∀ k : ℕ,
      (∑ a : Fin r with a.val < k, rowDeg m a) ≤ ∑ a : Fin r with a.val < k, rowNu (r := r) ν a := by sorry
