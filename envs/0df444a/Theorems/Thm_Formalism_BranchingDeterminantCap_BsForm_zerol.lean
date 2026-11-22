-- Prove2me | Theorems.Thm_Formalism_BranchingDeterminantCap_BsForm_zerol
-- name    : Formalism.BranchingDeterminantCap.BsForm.zerol
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:20:43.423245+00:00
-- url     : https://prove2.me/theorems/ee2dc594-6c5c-4bad-af49-a4e57202dea0
-- title:
--   Bs Form: zerol
-- statement:
--   The Bs Form construction uses the zerol property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchScale.lean#L164-L166
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchScale.lean#L164-L166

import Definitions.Def_Formalism_BranchSandwichDivisors_StatementW
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_BranchScale
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Formalism.GradedWeylDivisibility
open Formalism.REAL
noncomputable section
open Formalism Formalism.BranchingDeterminantCap
open Formalism.BranchingDeterminantCap.BsForm
variable {n : ℕ} {sg : Fin n → ℕ}
  {D : MvPolynomial (Fin n × Fin n) ℂ → MvPolynomial (Fin n × Fin n) ℂ → ℂ}

theorem Formalism.BranchingDeterminantCap.BsForm.zerol (H : BsForm sg D) (q) : D 0 q = 0 := by sorry
