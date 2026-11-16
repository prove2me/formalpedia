-- Prove2me | Theorems.Thm_APFPaper5_K1_CoarseBook_coarse_not_novel
-- name    : APFPaper5.K1.CoarseBook.coarse_not_novel
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-15T23:50:04.546402+00:00
-- url     : https://prove2.me/theorems/445ce512-2a3c-4511-81da-9f7d71b1231d
-- title:
--   Coarse record book: no addition to a nonempty coarse family is support-novel
-- statement:
--   In the coarse record book, in the coarse book, no distinction is support-novel over a nonempty family.
--
--   Publication scope: These are finite table-form claims with identity role exchange. They do not construct the physical ordered score, its alternating part, a general boundary-role isomorphism, K3 profile binding, K2-K6, or Born. These are record books, not worlds of all eight forms. The cheap book does not have each index novel over all the others, so it is not a counterexample to the counted-family bridge or its bound. Formal label count is not support-independent capacity count.
-- source:
--   ['C:/Users/brook/My Drive/__APF Library/Artifacts_2026-11-15_session/astra/sib_v66_publication/source/Theorems/Thm_APFPaper5_K1_shared_record_books.lean:106 (source SHA256 5f2cb8a13ff5f70388d8fcbe769e915f32b0045b3cbc71e484dc68159d75b9d4; APFPaper5.K1.CoarseBook.coarse_not_novel)', 'C:/Users/brook/My Drive/__APF Library/Artifacts_2026-11-15_session/astra/sib_v66_publication/reviews/rv2_v66_v22_review.json (SHA256 365ce42aeeada41fa76b7443fe2b5af6017c7fdeb2bb28169266b6dbba622948; modules[Theorems.Thm_APFPaper5_K1_shared_record_books].declarations[APFPaper5.K1.CoarseBook.coarse_not_novel])']

import Definitions.Def_APFPaper5_K1_shared_record_books_Vocabulary
import Definitions.Def_APFPaper5_K1_table_kernel_and_support_Vocabulary
import Theorems.Thm_APFPaper5_K1_atomTable_form_eq_zero_iff
import Theorems.Thm_APFPaper5_K1_atomTable_faithful_iff
import Theorems.Thm_APFPaper5_K1_atomTable_row_eq_of_same_marks
import Theorems.Thm_APFPaper5_K1_atomTable_merge_of_same_marks
import Theorems.Thm_APFPaper5_K1_atomTable_eq_zero_of_disjoint
import Theorems.Thm_APFPaper5_K1_card_mul_le_sum_of_private
import Theorems.Thm_APFPaper1_Source_sum_needed_le_bill
import Theorems.Thm_APFPaper1_Source_familyCost_eq_sum_of_available
import Theorems.Thm_APFPaper1_Source_supportNovel_of_private_record
import Theorems.Thm_APFPaper1_Source_supportNovel_of_private_record_count
import Theorems.Thm_APFPaper1_Source_marginal_ge_of_private_record
import Theorems.Thm_APFPaper1_Source_each_private_excludes_riding
import Theorems.Thm_APFPaper1_Source_supportNovel_of_each_private
import Theorems.Thm_APFPaper1_Source_marginal_zero_of_no_own_record
import Theorems.Thm_APFPaper1_Source_needs_own_record_of_supportNovel
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

set_option autoImplicit false
open APFPaper1.Source
namespace APFPaper5.K1
end APFPaper5.K1
open APFPaper5.K1
universe u v



/-! ### The coarse book: n distinctions, one record -/

namespace CoarseBook
end CoarseBook
open CoarseBook

theorem APFPaper5.K1.CoarseBook.coarse_not_novel (n : ℕ) (S : Finset (Fin n)) (hS : S.Nonempty) (d : Fin n) :
    ¬ supportNovel (D := Fin n) (P := Finset Unit) (R := Finset Unit) (Record := Unit)
        (fun p => p) (fun r => ∑ a ∈ r, w a) (fun p => (↑p : Set Unit))
        (fun _ sigma e => (↑(fam n e) : Set Unit) ⊆ sigma) (fun _ _ _ => True) S d := by sorry
