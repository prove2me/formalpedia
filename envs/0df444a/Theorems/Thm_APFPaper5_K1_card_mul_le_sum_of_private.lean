-- Prove2me | Theorems.Thm_APFPaper5_K1_card_mul_le_sum_of_private
-- name    : APFPaper5.K1.card_mul_le_sum_of_private
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-15T23:29:07.596502+00:00
-- url     : https://prove2.me/theorems/0e30c92f-a3c8-48a7-b168-5add05f53538
-- title:
--   Private records bound family cardinality times their floor
-- statement:
--   With nonnegative atom weights, if every member of S has a record needed by no other member of S and weighted at least eps, then card(S) times eps is at most the cost of S's support union. Dividing by eps would additionally require eps positive.
--
--   Publication scope: These are finite table-form claims with identity role exchange. They do not construct the physical ordered score, its alternating part, a general boundary-role isomorphism, K3 profile binding, K2-K6, or Born. Finite marks/atoms, hw and the particular hsame/hdisj/hpriv assumptions must be retained. The row-equality lemma uses nonzero weights and does not require their positivity. Division by eps requires eps positive; the formal bound itself is multiplicative. No physical score or general dimension bound is established.
-- source:
--   ['C:/Users/brook/My Drive/__APF Library/Artifacts_2026-11-15_session/astra/sib_v66_publication/source/Theorems/Thm_APFPaper5_K1_table_kernel_and_support.lean:133 (source SHA256 61e587dcab90d100333ed0e03852e7348044a522c28c7c516f691ae0d282561d; APFPaper5.K1.card_mul_le_sum_of_private)', 'C:/Users/brook/My Drive/__APF Library/Artifacts_2026-11-15_session/astra/sib_v66_publication/reviews/rv2_v66_v22_review.json (SHA256 365ce42aeeada41fa76b7443fe2b5af6017c7fdeb2bb28169266b6dbba622948; modules[Theorems.Thm_APFPaper5_K1_table_kernel_and_support].declarations[APFPaper5.K1.card_mul_le_sum_of_private])']

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

omit [Fintype ι] [Fintype W] in

theorem APFPaper5.K1.card_mul_le_sum_of_private [DecidableEq W] [DecidableEq ι] (w : W → ℝ)
    (hw : ∀ a, 0 ≤ w a) (fam : ι → Finset W) (S : Finset ι) (eps : ℝ)
    (hpriv : ∀ d ∈ S, ∃ a ∈ fam d, eps ≤ w a ∧ ∀ e ∈ S, e ≠ d → a ∉ fam e) :
    (S.card : ℝ) * eps ≤ ∑ a ∈ S.biUnion fam, w a := by sorry
