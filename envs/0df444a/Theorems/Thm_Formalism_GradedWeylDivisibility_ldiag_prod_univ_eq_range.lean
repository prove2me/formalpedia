-- Prove2me | Theorems.Thm_Formalism_GradedWeylDivisibility_ldiag_prod_univ_eq_range
-- name    : Formalism.GradedWeylDivisibility.ldiag_prod_univ_eq_range
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:59:47.696546+00:00
-- url     : https://prove2.me/theorems/37539250-19b7-4074-b8a3-88949cac2941
-- title:
--   Graded Weyl Divisibility: ldiag prod univ eq range
-- statement:
--   The Graded Weyl Divisibility construction uses the ldiag prod univ eq range property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/DomPow.lean#L86-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/DomPow.lean#L86-L90

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementA
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_DomPow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.GradedWeylDivisibility

theorem Formalism.GradedWeylDivisibility.ldiag_prod_univ_eq_range {r : ℕ} (t : Fin r → ℝ) (μ : Fin r → ℕ) :
    ∏ a : Fin r, t a ^ μ a = ∏ a ∈ range r, ldiagExt t a ^ ldiagExt μ a := by sorry
