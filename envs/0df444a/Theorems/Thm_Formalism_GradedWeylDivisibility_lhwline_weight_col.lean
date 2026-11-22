-- Prove2me | Theorems.Thm_Formalism_GradedWeylDivisibility_lhwline_weight_col
-- name    : Formalism.GradedWeylDivisibility.lhwline_weight_col
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T17:22:43.654628+00:00
-- url     : https://prove2.me/theorems/50ebd961-6491-4938-ad75-56e39910ec75
-- title:
--   Graded Weyl Divisibility: lhwline weight col
-- statement:
--   The Graded Weyl Divisibility construction uses the lhwline weight col property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/LHwlineLemmas.lean#L402-L406
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/LHwlineLemmas.lean#L402-L406

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

theorem Formalism.GradedWeylDivisibility.lhwline_weight_col (m : Fin r × Fin n →₀ ℕ) (j : Fin n) :
    Finsupp.weight (colW r n) m j = ∑ a : Fin r, m (a, j) := by sorry
