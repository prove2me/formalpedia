-- Prove2me | Theorems.Thm_Formalism_GradedWeylDivisibility_lgraded_multi
-- name    : Formalism.GradedWeylDivisibility.lgraded_multi
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:23:09.170359+00:00
-- url     : https://prove2.me/theorems/a06ab446-5201-440c-a8ad-af7f4f1c84a8
-- title:
--   Graded Weyl Divisibility: lgraded multi
-- statement:
--   The Graded Weyl Divisibility construction uses the lgraded multi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/LGradedLemmas.lean#L113-L128
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/LGradedLemmas.lean#L113-L128

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

theorem Formalism.GradedWeylDivisibility.lgraded_multi {r n : ℕ} (M : Submodule ℚ (MvPolynomial (Fin r × Fin n) ℚ)) (hM : RowDivClosed M)
    (μ : Fin r → ℕ) (A : Finset (Fin r)) :
    ∀ f ∈ M, ∃ h ∈ M, ∀ m, coeff m h =
      if (∀ a ∈ A, Finsupp.weight (lgraded_wa a) m = μ a) then coeff m f else 0 := by sorry
