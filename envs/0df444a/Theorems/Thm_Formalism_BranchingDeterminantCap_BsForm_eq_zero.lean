-- Prove2me | Theorems.Thm_Formalism_BranchingDeterminantCap_BsForm_eq_zero
-- name    : Formalism.BranchingDeterminantCap.BsForm.eq_zero
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T00:41:29.045114+00:00
-- url     : https://prove2.me/theorems/dad79a39-3dc6-4ca0-a9c9-17b5dc30f35b
-- title:
--   Bs Form: eq zero
-- statement:
--   The Bs Form construction uses the eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchScale.lean#L260-L282
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchScale.lean#L260-L282

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

theorem Formalism.BranchingDeterminantCap.BsForm.eq_zero (H : BsForm sg D) (hsg : Antitone sg)
    (h0 : D (hw ℂ le_rfl sg) (hw ℂ le_rfl sg) = 0) :
    ∀ p ∈ dualWeyl ℂ n n sg, ∀ q ∈ dualWeyl ℂ n n sg, D p q = 0 := by sorry
