-- Prove2me | Theorems.Thm_Formalism_GradedWeylDivisibility_rowPart_add
-- name    : Formalism.GradedWeylDivisibility.rowPart_add
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T17:11:42.277497+00:00
-- url     : https://prove2.me/theorems/ff8261fa-6ed8-4a38-8088-2c4ce31ac55f
-- title:
--   Graded Weyl Divisibility: row Part add
-- statement:
--   The Graded Weyl Divisibility construction uses the row Part add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/LBidetdomLemmas.lean#L70-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/LBidetdomLemmas.lean#L70-L72

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

theorem Formalism.GradedWeylDivisibility.rowPart_add {r n : ℕ} (k : ℕ) (m m' : Fin r × Fin n →₀ ℕ) :
    rowPart k (m + m') = rowPart k m + rowPart k m' := by sorry
