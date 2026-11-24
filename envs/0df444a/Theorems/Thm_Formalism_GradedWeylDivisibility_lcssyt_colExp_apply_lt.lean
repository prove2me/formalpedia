-- Prove2me | Theorems.Thm_Formalism_GradedWeylDivisibility_lcssyt_colExp_apply_lt
-- name    : Formalism.GradedWeylDivisibility.lcssyt_colExp_apply_lt
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:59:37.459546+00:00
-- url     : https://prove2.me/theorems/feaadced-9a2f-43a4-8603-2925254a6c5d
-- title:
--   Graded Weyl Divisibility: lcssyt col Exp apply lt
-- statement:
--   The Graded Weyl Divisibility construction uses the lcssyt col Exp apply lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/LCssytLemmas.lean#L34-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/LCssytLemmas.lean#L34-L50

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

theorem Formalism.GradedWeylDivisibility.lcssyt_colExp_apply_lt {r n h : ℕ} (c : Fin h → Fin r) (hh : h ≤ n) (a : Fin r) (t : Fin n)
    (ht : t.val < h) : colExp c hh (a, t) = if c ⟨t.val, ht⟩ = a then 1 else 0 := by sorry
