-- Prove2me | Theorems.Thm_Formalism_BranchingDeterminantCap_BsForm_sumr
-- name    : Formalism.BranchingDeterminantCap.BsForm.sumr
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:17:16.236784+00:00
-- url     : https://prove2.me/theorems/32379fd2-d4e5-479a-aa86-df1cc7b46cba
-- title:
--   Bs Form: sumr
-- statement:
--   The Bs Form construction uses the sumr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchScale.lean#L179-L184
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchScale.lean#L179-L184

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

theorem Formalism.BranchingDeterminantCap.BsForm.sumr (H : BsForm sg D) {ι : Type*} (s : Finset ι) (g : ι → MvPolynomial (Fin n × Fin n) ℂ) (p) :
    D p (∑ i ∈ s, g i) = ∑ i ∈ s, D p (g i) := by sorry
