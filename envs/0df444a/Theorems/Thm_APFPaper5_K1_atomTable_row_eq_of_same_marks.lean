-- Prove2me | Theorems.Thm_APFPaper5_K1_atomTable_row_eq_of_same_marks
-- name    : APFPaper5.K1.atomTable_row_eq_of_same_marks
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-15T23:29:06.501684+00:00
-- url     : https://prove2.me/theorems/248573bc-5fe0-477a-88d7-c557aa6cb9b1
-- title:
--   Marks agreeing at nonzero atoms have equal table rows
-- statement:
--   If two marks agree on every atom whose weight is nonzero, their atom-table entries against any third mark are equal. Nonnegative weights are not required for this row identity.
--
--   Publication scope: These are finite table-form claims with identity role exchange. They do not construct the physical ordered score, its alternating part, a general boundary-role isomorphism, K3 profile binding, K2-K6, or Born. Finite marks/atoms, hw and the particular hsame/hdisj/hpriv assumptions must be retained. The row-equality lemma uses nonzero weights and does not require their positivity. Division by eps requires eps positive; the formal bound itself is multiplicative. No physical score or general dimension bound is established.
-- source:
--   ['C:/Users/brook/My Drive/__APF Library/Artifacts_2026-11-15_session/astra/sib_v66_publication/source/Theorems/Thm_APFPaper5_K1_table_kernel_and_support.lean:86 (source SHA256 61e587dcab90d100333ed0e03852e7348044a522c28c7c516f691ae0d282561d; APFPaper5.K1.atomTable_row_eq_of_same_marks)', 'C:/Users/brook/My Drive/__APF Library/Artifacts_2026-11-15_session/astra/sib_v66_publication/reviews/rv2_v66_v22_review.json (SHA256 365ce42aeeada41fa76b7443fe2b5af6017c7fdeb2bb28169266b6dbba622948; modules[Theorems.Thm_APFPaper5_K1_table_kernel_and_support].declarations[APFPaper5.K1.atomTable_row_eq_of_same_marks])']

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

omit [Fintype ι] in

theorem APFPaper5.K1.atomTable_row_eq_of_same_marks (w : W → ℝ) (mark : ι → W → Bool) (i j : ι)
    (hsame : ∀ a, w a ≠ 0 → mark i a = mark j a) (k : ι) :
    atomTable w mark i k = atomTable w mark j k := by sorry
