-- Prove2me | Theorems.Thm_Formalism_GradedWeylDivisibility_lgraded_euler_monomial
-- name    : Formalism.GradedWeylDivisibility.lgraded_euler_monomial
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:20:42.317902+00:00
-- url     : https://prove2.me/theorems/8b735cfc-ee56-4cfb-a847-aba792de8793
-- title:
--   Graded Weyl Divisibility: lgraded euler monomial
-- statement:
--   The Graded Weyl Divisibility construction uses the lgraded euler monomial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/LGradedLemmas.lean#L38-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/LGradedLemmas.lean#L38-L41

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

theorem Formalism.GradedWeylDivisibility.lgraded_euler_monomial {r n : ℕ} (a : Fin r) (m : Fin r × Fin n →₀ ℕ) (c : ℚ) :
    rowDiv ℚ a a 1 (monomial m c) = ((Finsupp.weight (lgraded_wa a) m : ℕ) : ℚ) • monomial m c := by sorry
