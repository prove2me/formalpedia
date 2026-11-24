-- Prove2me | Theorems.Thm_Formalism_GradedWeylDivisibility_lehw_eval_idFrame_hw
-- name    : Formalism.GradedWeylDivisibility.lehw_eval_idFrame_hw
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:11:30.145736+00:00
-- url     : https://prove2.me/theorems/1298c7f6-6e0b-4800-be5b-1ca5be0d8feb
-- title:
--   Graded Weyl Divisibility: lehw eval id Frame hw
-- statement:
--   The Graded Weyl Divisibility construction uses the lehw eval id Frame hw property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/FockQHW.lean#L10-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/FockQHW.lean#L10-L22

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementE
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LEhwLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_FockQHW
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

theorem Formalism.GradedWeylDivisibility.lehw_eval_idFrame_hw {r n : ℕ} (hn : n ≤ r) (ν : Fin n → ℕ) :
    eval (idFrame ℚ r n) (hw ℚ hn ν) = 1 := by sorry
