-- Prove2me | Theorems.Thm_Formalism_BranchingDeterminantCap_BsForm_hw_weight
-- name    : Formalism.BranchingDeterminantCap.BsForm.hw_weight
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:12:28.283486+00:00
-- url     : https://prove2.me/theorems/04de893e-baa5-4771-98c9-14fd4b77a3c5
-- title:
--   Bs Form: hw weight
-- statement:
--   The Bs Form construction uses the hw weight property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchScale.lean#L186-L219
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchScale.lean#L186-L219

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

theorem Formalism.BranchingDeterminantCap.BsForm.hw_weight (H : BsForm sg D) (hsg : Antitone sg) (μ : Fin n → ℕ) (hμ : μ ≠ sg)
    (q : MvPolynomial (Fin n × Fin n) ℂ) (hq : q ∈ dualWeyl ℂ n n sg)
    (hqw : IsWeightedHomogeneous (rowW n n) q μ) : D (hw ℂ le_rfl sg) q = 0 := by sorry
