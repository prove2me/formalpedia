-- Prove2me | Theorems.Thm_Formalism_GradedWeylDivisibility_rowTot_add
-- name    : Formalism.GradedWeylDivisibility.rowTot_add
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T17:15:39.70074+00:00
-- url     : https://prove2.me/theorems/7f3144ea-38c6-4279-a1c9-602a43496bc2
-- title:
--   Graded Weyl Divisibility: row Tot add
-- statement:
--   The Graded Weyl Divisibility construction uses the row Tot add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/LBidetdomLemmas.lean#L87-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/LBidetdomLemmas.lean#L87-L89

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

theorem Formalism.GradedWeylDivisibility.rowTot_add {r n : ℕ} (m m' : Fin r × Fin n →₀ ℕ) :
    rowTot (m + m') = rowTot m + rowTot m' := by sorry
