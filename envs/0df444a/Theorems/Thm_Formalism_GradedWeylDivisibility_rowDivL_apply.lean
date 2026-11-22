-- Prove2me | Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- name    : Formalism.GradedWeylDivisibility.rowDivL_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T16:56:39.466466+00:00
-- url     : https://prove2.me/theorems/05e216f5-342e-4f48-8560-a0298465a305
-- title:
--   Graded Weyl Divisibility: row Div L apply
-- statement:
--   The Graded Weyl Divisibility construction uses the row Div L apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/LRowdivLemmas.lean#L25-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/LRowdivLemmas.lean#L25-L26

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementA
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LRowdivLemmas
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

theorem Formalism.GradedWeylDivisibility.rowDivL_apply (R : Type*) [CommRing R] {r n : ℕ} (a b : Fin r) (k : ℕ)
    (f : MvPolynomial (Fin r × Fin n) R) : rowDivL R a b k f = rowDiv R a b k f := by sorry

attribute [defeq] Formalism.GradedWeylDivisibility.rowDivL_apply
