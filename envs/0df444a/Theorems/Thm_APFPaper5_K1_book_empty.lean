-- Prove2me | Theorems.Thm_APFPaper5_K1_book_empty
-- name    : APFPaper5.K1.book_empty
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-15T22:31:46.675192+00:00
-- url     : https://prove2.me/theorems/9c5dbd40-831a-4497-896d-f4d77a7dca00
-- title:
--   The empty subset's book weight is zero
-- statement:
--   For any cost function on finite families, book(f,empty) equals zero.
--
--   Publication scope: These are finite table-form claims with identity role exchange. They do not construct the physical ordered score, its alternating part, a general boundary-role isomorphism, K3 profile binding, K2-K6, or Born. The book is a signed algebraic representation, not a positive physical record ledger. All weights need not be nonnegative; the empty offset is carried on the universal record for the table identity. No protocol-bill representation, uniqueness theorem or completely-alternating characterization is proved.
-- source:
--   ['C:/Users/brook/My Drive/__APF Library/Artifacts_2026-11-15_session/astra/sib_v66_publication/source/Theorems/Thm_APFPaper5_K1_cost_book.lean:107 (source SHA256 88667832d19995dd1e5de3f3f99b527fb47ae2c9b76133e5a230f87fffccd8e2; APFPaper5.K1.book_empty)', 'C:/Users/brook/My Drive/__APF Library/Artifacts_2026-11-15_session/astra/sib_v66_publication/reviews/rv2_v66_v22_review.json (SHA256 365ce42aeeada41fa76b7443fe2b5af6017c7fdeb2bb28169266b6dbba622948; modules[Theorems.Thm_APFPaper5_K1_cost_book].declarations[APFPaper5.K1.book_empty])']

import Definitions.Def_APFPaper5_K1_cost_book_Vocabulary
import Theorems.Thm_APFPaper5_K1_atomTable_symm
import Theorems.Thm_APFPaper5_K1_atomTable_form
import Theorems.Thm_APFPaper5_K1_atomTable_nonneg
import Theorems.Thm_APFPaper5_K1_record_book_table_satisfies_K1
import Definitions.Def_APFPaper5_K1_SharedCost
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false

namespace APFPaper5.K1
end APFPaper5.K1
open APFPaper5.K1
variable {ι : Type} [DecidableEq ι]







variable [Fintype ι]

theorem APFPaper5.K1.book_empty (f : Finset ι → ℝ) : book f ∅ = 0 := by sorry
