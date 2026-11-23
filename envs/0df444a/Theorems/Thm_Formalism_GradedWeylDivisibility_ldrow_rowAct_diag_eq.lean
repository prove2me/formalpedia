-- Prove2me | Theorems.Thm_Formalism_GradedWeylDivisibility_ldrow_rowAct_diag_eq
-- name    : Formalism.GradedWeylDivisibility.ldrow_rowAct_diag_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:52:50.750934+00:00
-- url     : https://prove2.me/theorems/5f91e198-097f-48cc-99a8-65c7eaf61a7c
-- title:
--   Graded Weyl Divisibility: ldrow row Act diag eq
-- statement:
--   The Graded Weyl Divisibility construction uses the ldrow row Act diag eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/LDrowLemmas.lean#L9-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/LDrowLemmas.lean#L9-L14

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementD
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LDrowLemmas
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Finset
noncomputable section
open Formalism Formalism.GradedWeylDivisibility

theorem Formalism.GradedWeylDivisibility.ldrow_rowAct_diag_eq {R : Type*} [CommRing R] {k n : ℕ} (t : Fin k → R) :
    rowAct R (n := n) (Matrix.diagonal t) = aeval fun v : Fin k × Fin n => C (t v.1) * X v := by sorry
