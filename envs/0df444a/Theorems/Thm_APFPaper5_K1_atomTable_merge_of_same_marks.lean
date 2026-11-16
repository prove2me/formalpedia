-- Prove2me | Theorems.Thm_APFPaper5_K1_atomTable_merge_of_same_marks
-- name    : APFPaper5.K1.atomTable_merge_of_same_marks
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-15T23:29:09.470207+00:00
-- url     : https://prove2.me/theorems/c86265ae-d53c-40e1-aa84-5881c5ca1081
-- title:
--   Distinct marks identical on positive atoms yield a null difference
-- statement:
--   With nonnegative weights, distinct mark indices agreeing at all positive-weight atoms have a markDiff vector of zero diagonal form, and the table fails FaithfulNonnegDiagonal.
--
--   Publication scope: These are finite table-form claims with identity role exchange. They do not construct the physical ordered score, its alternating part, a general boundary-role isomorphism, K3 profile binding, K2-K6, or Born. Finite marks/atoms, hw and the particular hsame/hdisj/hpriv assumptions must be retained. The row-equality lemma uses nonzero weights and does not require their positivity. Division by eps requires eps positive; the formal bound itself is multiplicative. No physical score or general dimension bound is established.
-- source:
--   ['C:/Users/brook/My Drive/__APF Library/Artifacts_2026-11-15_session/astra/sib_v66_publication/source/Theorems/Thm_APFPaper5_K1_table_kernel_and_support.lean:102 (source SHA256 61e587dcab90d100333ed0e03852e7348044a522c28c7c516f691ae0d282561d; APFPaper5.K1.atomTable_merge_of_same_marks)', 'C:/Users/brook/My Drive/__APF Library/Artifacts_2026-11-15_session/astra/sib_v66_publication/reviews/rv2_v66_v22_review.json (SHA256 365ce42aeeada41fa76b7443fe2b5af6017c7fdeb2bb28169266b6dbba622948; modules[Theorems.Thm_APFPaper5_K1_table_kernel_and_support].declarations[APFPaper5.K1.atomTable_merge_of_same_marks])']

import Definitions.Def_APFPaper5_K1_table_kernel_and_support_Vocabulary
import Theorems.Thm_APFPaper5_K1_atomTable_symm
import Theorems.Thm_APFPaper5_K1_atomTable_form
import Theorems.Thm_APFPaper5_K1_atomTable_nonneg
import Theorems.Thm_APFPaper5_K1_record_book_table_satisfies_K1
import Theorems.Thm_APFPaper5_K1_familyCost_weighted
import Theorems.Thm_APFPaper5_K1_recordModelCost_eq
import Theorems.Thm_APFPaper5_K1_recordModel_sharedCost
import Theorems.Thm_APFPaper5_K1_recordModel_satisfies_K1
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false
namespace APFPaper5.K1
end APFPaper5.K1
open APFPaper5
open APFPaper5.K1
universe u v
variable {ι : Type u} [Fintype ι] {W : Type v} [Fintype W]

theorem APFPaper5.K1.atomTable_merge_of_same_marks [DecidableEq ι] (w : W → ℝ) (hw : ∀ a, 0 ≤ w a)
    (mark : ι → W → Bool) (i j : ι) (hij : i ≠ j)
    (hsame : ∀ a, 0 < w a → mark i a = mark j a) :
    tableForm (atomTable w mark) (markDiff i j) (markDiff i j) = 0 ∧
      ¬ FaithfulNonnegDiagonal (tableForm (atomTable w mark)) (LinearEquiv.refl ℝ (ι → ℝ)) := by sorry
