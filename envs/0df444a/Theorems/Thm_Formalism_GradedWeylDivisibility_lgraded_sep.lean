-- Prove2me | Theorems.Thm_Formalism_GradedWeylDivisibility_lgraded_sep
-- name    : Formalism.GradedWeylDivisibility.lgraded_sep
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:23:14.253798+00:00
-- url     : https://prove2.me/theorems/0335ad78-34ac-45e0-8192-54d705b7494a
-- title:
--   Graded Weyl Divisibility: lgraded sep
-- statement:
--   The Graded Weyl Divisibility construction uses the lgraded sep property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/LGradedLemmas.lean#L81-L111
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/LGradedLemmas.lean#L81-L111

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

theorem Formalism.GradedWeylDivisibility.lgraded_sep {r n : ℕ} (M : Submodule ℚ (MvPolynomial (Fin r × Fin n) ℚ)) (hM : RowDivClosed M)
    (a : Fin r) (V : Finset ℕ) :
    ∀ f ∈ M, (∀ m ∈ f.support, Finsupp.weight (lgraded_wa a) m ∈ V) →
      ∀ t, weightedHomogeneousComponent (lgraded_wa a) t f ∈ M := by sorry
