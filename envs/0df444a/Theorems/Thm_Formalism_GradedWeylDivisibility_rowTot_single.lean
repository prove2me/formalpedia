-- Prove2me | Theorems.Thm_Formalism_GradedWeylDivisibility_rowTot_single
-- name    : Formalism.GradedWeylDivisibility.rowTot_single
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:22:37.205911+00:00
-- url     : https://prove2.me/theorems/d2e53934-450c-426f-9cc7-c8a1494c563b
-- title:
--   Graded Weyl Divisibility: row Tot single
-- statement:
--   The Graded Weyl Divisibility construction uses the row Tot single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/LBidetdomLemmas.lean#L91-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/LBidetdomLemmas.lean#L91-L96

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementA
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LBidetdomLemmas
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

theorem Formalism.GradedWeylDivisibility.rowTot_single {r n : ℕ} (b : Fin r) (s : Fin n) :
    rowTot (Finsupp.single (b, s) 1 : Fin r × Fin n →₀ ℕ) = 1 := by sorry
