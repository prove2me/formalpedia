-- Prove2me | Theorems.Thm_Formalism_BranchingDeterminantCap_BsForm_rad_rowDiv
-- name    : Formalism.BranchingDeterminantCap.BsForm.rad_rowDiv
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:12:35.531084+00:00
-- url     : https://prove2.me/theorems/275b940e-22a6-4dcf-90fd-8ed0a74fa0ad
-- title:
--   Bs Form: rad row Div
-- statement:
--   The Bs Form construction uses the rad row Div property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchScale.lean#L236-L258
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchScale.lean#L236-L258

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

theorem Formalism.BranchingDeterminantCap.BsForm.rad_rowDiv (H : BsForm sg D) (p : MvPolynomial (Fin n × Fin n) ℂ) (hp : p ∈ dualWeyl ℂ n n sg)
    (h0 : ∀ q ∈ dualWeyl ℂ n n sg, D p q = 0) (a b : Fin n) (k : ℕ) :
    ∀ q ∈ dualWeyl ℂ n n sg, D (rowDiv ℂ a b k p) q = 0 := by sorry
