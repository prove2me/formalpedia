-- Prove2me | Theorems.Thm_Formalism_GradedWeylDivisibility_rowDeg_add
-- name    : Formalism.GradedWeylDivisibility.rowDeg_add
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T17:09:02.699231+00:00
-- url     : https://prove2.me/theorems/c3721072-36d8-439e-9ac6-e6686c273223
-- title:
--   Graded Weyl Divisibility: row Deg add
-- statement:
--   The Graded Weyl Divisibility construction uses the row Deg add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/LBidetdomLemmas.lean#L48-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/LBidetdomLemmas.lean#L48-L50

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

theorem Formalism.GradedWeylDivisibility.rowDeg_add {r n : ℕ} (m m' : Fin r × Fin n →₀ ℕ) (a : Fin r) :
    rowDeg (m + m') a = rowDeg m a + rowDeg m' a := by sorry
