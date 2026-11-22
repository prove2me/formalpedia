-- Prove2me | Theorems.Thm_Formalism_GradedWeylDivisibility_rowDeg_single
-- name    : Formalism.GradedWeylDivisibility.rowDeg_single
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T17:09:22.601397+00:00
-- url     : https://prove2.me/theorems/e0ff18d9-698d-4187-8519-05675e375b69
-- title:
--   Graded Weyl Divisibility: row Deg single
-- statement:
--   The Graded Weyl Divisibility construction uses the row Deg single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/LBidetdomLemmas.lean#L55-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/LBidetdomLemmas.lean#L55-L62

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

theorem Formalism.GradedWeylDivisibility.rowDeg_single {r n : ℕ} (b a : Fin r) (s : Fin n) :
    rowDeg (Finsupp.single (b, s) 1) a = if b = a then 1 else 0 := by sorry
