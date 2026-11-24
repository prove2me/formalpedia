-- Prove2me | Theorems.Thm_Formalism_GradedWeylDivisibility_lctwo_le_weight
-- name    : Formalism.GradedWeylDivisibility.lctwo_le_weight
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:59:35.387529+00:00
-- url     : https://prove2.me/theorems/a09d7b37-5e66-4be5-a8eb-744b9f540db1
-- title:
--   Graded Weyl Divisibility: lctwo le weight
-- statement:
--   The Graded Weyl Divisibility construction uses the lctwo le weight property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/TwoColumn.lean#L21-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/TwoColumn.lean#L21-L31

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementC
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_TwoColumn
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

theorem Formalism.GradedWeylDivisibility.lctwo_le_weight {r n : ℕ} {l j : Fin n} (hlj : l ≠ j) (d : Fin r × Fin n →₀ ℕ) (b : Fin r) :
    d (b, l) ≤ Finsupp.weight (pairW l j) d (b, l) ∧ d (b, j) ≤ Finsupp.weight (pairW l j) d (b, l) := by sorry
