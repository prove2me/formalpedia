-- Prove2me | Theorems.Thm_Formalism_GradedWeylDivisibility_lehw_weight_P
-- name    : Formalism.GradedWeylDivisibility.lehw_weight_P
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:06:34.546797+00:00
-- url     : https://prove2.me/theorems/3f332ef3-3604-471d-8cf5-0d322164b159
-- title:
--   Graded Weyl Divisibility: lehw weight P
-- statement:
--   The Graded Weyl Divisibility construction uses the lehw weight P property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/LEhwLemmas.lean#L176-L185
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/LEhwLemmas.lean#L176-L185

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

theorem Formalism.GradedWeylDivisibility.lehw_weight_P {r n : ℕ} (a : Fin r) (m : Fin r × Fin n →₀ ℕ) :
    Finsupp.weight (lehwP a) m = ((∑ a' : Fin r with a'.val < a.val + 1, rowDeg m a' : ℕ) : ℤ) := by sorry
