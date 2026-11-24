-- Prove2me | Theorems.Thm_Formalism_GradedWeylDivisibility_lgraded_rowGen_monomial
-- name    : Formalism.GradedWeylDivisibility.lgraded_rowGen_monomial
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:23:23.604732+00:00
-- url     : https://prove2.me/theorems/7e587997-db99-46b5-9418-ada0396df0c6
-- title:
--   Graded Weyl Divisibility: lgraded row Gen monomial
-- statement:
--   The Graded Weyl Divisibility construction uses the lgraded row Gen monomial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/LGradedLemmas.lean#L26-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/LGradedLemmas.lean#L26-L36

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementB
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LRowdivLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LGradedLemmas
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

theorem Formalism.GradedWeylDivisibility.lgraded_rowGen_monomial {r n : ℕ} (a : Fin r) (m : Fin r × Fin n →₀ ℕ) (c : ℚ) :
    rowGen ℚ a a (monomial m c) =
      Polynomial.C (monomial m c) * (1 + Polynomial.X) ^ (Finsupp.weight (lgraded_wa a) m) := by sorry
