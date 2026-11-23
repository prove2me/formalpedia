-- Prove2me | Theorems.Thm_Formalism_BranchingDeterminantCap_BsForm_hw_rad
-- name    : Formalism.BranchingDeterminantCap.BsForm.hw_rad
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T10:12:38.466887+00:00
-- url     : https://prove2.me/theorems/3fd4cfaa-13e0-4b33-87d8-31e17a6030a9
-- title:
--   Bs Form: hw rad
-- statement:
--   The Bs Form construction uses the hw rad property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchScale.lean#L221-L234
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchScale.lean#L221-L234

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

theorem Formalism.BranchingDeterminantCap.BsForm.hw_rad (H : BsForm sg D) (hsg : Antitone sg) (h0 : D (hw ℂ le_rfl sg) (hw ℂ le_rfl sg) = 0)
    (q : MvPolynomial (Fin n × Fin n) ℂ) (hq : q ∈ dualWeyl ℂ n n sg) : D (hw ℂ le_rfl sg) q = 0 := by sorry
