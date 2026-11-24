-- Prove2me | Theorems.Thm_Formalism_GradedWeylDivisibility_lhwline_elim_offdiag
-- name    : Formalism.GradedWeylDivisibility.lhwline_elim_offdiag
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:29:37.046245+00:00
-- url     : https://prove2.me/theorems/344e5739-fb87-4ea7-b1b2-b12932ec3c02
-- title:
--   Graded Weyl Divisibility: lhwline elim offdiag
-- statement:
--   The Graded Weyl Divisibility construction uses the lhwline elim offdiag property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/LHwlineLemmas.lean#L351-L361
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/LHwlineLemmas.lean#L351-L361

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementB
import Definitions.Def_Formalism_GradedWeylDivisibility_DualWeylDominanceOf
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LHwrowLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LHwlineLemmas
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
variable {K : Type} [Field K] {r n : ℕ}

theorem Formalism.GradedWeylDivisibility.lhwline_elim_offdiag [Infinite K] (x : Fin r × Fin n → K)
    (hx : ∀ (s : ℕ) (hr : s + 1 ≤ r) (hn : s + 1 ≤ n), eval x (lpMinor K (s + 1) hr hn) ≠ 0)
    (a : Fin r) (j : Fin n) (h : a.val ≠ j.val) : lhwline_elim (min r n) x (a, j) = 0 := by sorry
