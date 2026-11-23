-- Prove2me | Theorems.Thm_Formalism_BranchingDeterminantCap_bs_dom
-- name    : Formalism.BranchingDeterminantCap.bs_dom
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T10:25:44.307396+00:00
-- url     : https://prove2.me/theorems/78e40be5-3066-490e-9b22-6980792a8ff6
-- title:
--   Branching Determinant Cap: bs dom
-- statement:
--   The Branching Determinant Cap construction uses the bs dom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchScale.lean#L62-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchScale.lean#L62-L85

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

theorem Formalism.BranchingDeterminantCap.bs_dom {r n : ℕ} (ν : Fin n → ℕ) (f : MvPolynomial (Fin r × Fin n) ℂ)
    (hf : f ∈ dualWeyl ℂ r n ν) : ∀ m ∈ f.support,
      (∀ k : ℕ, (∑ a : Fin r with a.val < k, rowDeg m a) ≤ ∑ t : Fin n with t.val < k, ν t) ∧
      ∑ a : Fin r, rowDeg m a = ∑ t : Fin n, ν t := by sorry
