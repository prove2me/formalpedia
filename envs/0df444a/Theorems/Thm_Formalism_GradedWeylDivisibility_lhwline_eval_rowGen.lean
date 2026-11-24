-- Prove2me | Theorems.Thm_Formalism_GradedWeylDivisibility_lhwline_eval_rowGen
-- name    : Formalism.GradedWeylDivisibility.lhwline_eval_rowGen
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:23:39.394292+00:00
-- url     : https://prove2.me/theorems/1d38c3eb-dd8a-4b11-b744-3b31fca51b03
-- title:
--   Graded Weyl Divisibility: lhwline eval row Gen
-- statement:
--   The Graded Weyl Divisibility construction uses the lhwline eval row Gen property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/LHwlineLemmas.lean#L21-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/LHwlineLemmas.lean#L21-L35

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
variable {K : Type*} [Field K] {r n : ℕ}

theorem Formalism.GradedWeylDivisibility.lhwline_eval_rowGen (a b : Fin r) (t : K) (x : Fin r × Fin n → K)
    (g : MvPolynomial (Fin r × Fin n) K) :
    Polynomial.eval₂ (eval x) t (rowGen K a b g) = eval (lhwline_rowOp a b t x) g := by sorry
