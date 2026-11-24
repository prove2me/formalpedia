-- Prove2me | Theorems.Thm_Formalism_GradedWeylDivisibility_lcssyt_colExp_apply_ge
-- name    : Formalism.GradedWeylDivisibility.lcssyt_colExp_apply_ge
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:59:46.883842+00:00
-- url     : https://prove2.me/theorems/909df927-d69c-4c09-81bf-0e35d5f2d7a1
-- title:
--   Graded Weyl Divisibility: lcssyt col Exp apply ge
-- statement:
--   The Graded Weyl Divisibility construction uses the lcssyt col Exp apply ge property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/LCssytLemmas.lean#L52-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/LCssytLemmas.lean#L52-L62

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementC
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LCssytLemmas
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Finset
noncomputable section
open Formalism Formalism.GradedWeylDivisibility

theorem Formalism.GradedWeylDivisibility.lcssyt_colExp_apply_ge {r n h : ℕ} (c : Fin h → Fin r) (hh : h ≤ n) (a : Fin r) (t : Fin n)
    (ht : ¬ t.val < h) : colExp c hh (a, t) = 0 := by sorry
