-- Prove2me | Theorems.Thm_Formalism_GradedWeylDivisibility_lgraded_coeff_euler
-- name    : Formalism.GradedWeylDivisibility.lgraded_coeff_euler
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T02:53:13.256072+00:00
-- url     : https://prove2.me/theorems/5e474a60-cfa0-4d58-8d80-fdc380e7568a
-- title:
--   Graded Weyl Divisibility: lgraded coeff euler
-- statement:
--   The Graded Weyl Divisibility construction uses the lgraded coeff euler property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/LGradedLemmas.lean#L43-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/LGradedLemmas.lean#L43-L55

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

theorem Formalism.GradedWeylDivisibility.lgraded_coeff_euler {r n : ℕ} (a : Fin r) (f : MvPolynomial (Fin r × Fin n) ℚ)
    (m : Fin r × Fin n →₀ ℕ) :
    coeff m (rowDiv ℚ a a 1 f) = ((Finsupp.weight (lgraded_wa a) m : ℕ) : ℚ) * coeff m f := by sorry
