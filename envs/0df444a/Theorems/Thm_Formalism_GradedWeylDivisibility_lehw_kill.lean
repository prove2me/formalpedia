-- Prove2me | Theorems.Thm_Formalism_GradedWeylDivisibility_lehw_kill
-- name    : Formalism.GradedWeylDivisibility.lehw_kill
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:07:01.476908+00:00
-- url     : https://prove2.me/theorems/7422d03f-920d-4fd5-b531-0ec4f2966da7
-- title:
--   Graded Weyl Divisibility: lehw kill
-- statement:
--   The Graded Weyl Divisibility construction uses the lehw kill property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/LEhwLemmas.lean#L198-L216
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/LEhwLemmas.lean#L198-L216

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

theorem Formalism.GradedWeylDivisibility.lehw_kill {r n : ℕ} (hn : n ≤ r) (ν : Fin n → ℕ) (hν : Antitone ν)
    (G : MvPolynomial (Fin r × Fin n) ℚ) (hG : G ∈ dualWeyl ℚ r n ν)
    (hGh : IsWeightedHomogeneous (rowW r n) G (rowNu (r := r) ν))
    (a b : Fin r) (hab : a < b) (k : ℕ) (hk : 1 ≤ k) : rowDiv ℚ a b k G = 0 := by sorry
