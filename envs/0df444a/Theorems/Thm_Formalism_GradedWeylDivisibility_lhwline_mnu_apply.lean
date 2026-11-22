-- Prove2me | Theorems.Thm_Formalism_GradedWeylDivisibility_lhwline_mnu_apply
-- name    : Formalism.GradedWeylDivisibility.lhwline_mnu_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T17:24:36.687586+00:00
-- url     : https://prove2.me/theorems/a99dce14-855b-42c6-be70-addefff8256a
-- title:
--   Graded Weyl Divisibility: lhwline mnu apply
-- statement:
--   The Graded Weyl Divisibility construction uses the lhwline mnu apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/LHwlineLemmas.lean#L426-L442
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/LHwlineLemmas.lean#L426-L442

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

theorem Formalism.GradedWeylDivisibility.lhwline_mnu_apply (hn : n ≤ r) (ν : Fin n → ℕ) (a : Fin r) (j : Fin n) :
    lhwline_mnu hn ν (a, j) = if a.val = j.val then ν j else 0 := by sorry
