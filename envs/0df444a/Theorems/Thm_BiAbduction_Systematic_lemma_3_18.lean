-- Prove2me | Theorems.Thm_BiAbduction_Systematic_lemma_3_18
-- name    : BiAbduction.Systematic.lemma_3_18
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T03:15:08.013099+00:00
-- url     : https://prove2.me/theorems/51bf9dce-fcb2-46d8-80d8-d4922597ced1
-- title:
--   Lemma 3.18 — termination: for all Δ, H some Δ ∗ [D] ▷ H is derivable, found by a terminating search
-- statement:
--   There is an algorithm which, given any quantifier-free left-hand side $\Delta$ and any symbolic heap $H$ of the Points-to Instantiation, returns a disjunction $D$ such that
--   $$\Delta*[D]\triangleright H$$
--   is derivable with the rules of Figure 2. In particular such a $D$ exists for every $\Delta$ and $H$, and the proof search terminates.
--
--   **Formalization Note** "The proof search is terminating" is read as: the search is a total computable function `search : LHS → SH → Disj` (Mathlib's `Computable₂` for the standard encodings of lists, pairs, sums, booleans and naturals) whose output is always derivable.
-- source:
--   Calcagno, Distefano, O'Hearn, Yang, Compositional Shape Analysis by means of Bi-Abduction, J. ACM (2011), p. 29, Lemma 3.18

import Mathlib
import Definitions.Def_BiAbduction_Systematic_Rules

namespace BiAbduction.Systematic

/-- Lemma 3.18 (p. 29). For every `Δ` and `H` some `D` with `Δ ∗ [D] ▷ H` is derivable, and the
proof search terminates: such a `D` is produced by a total computable function. -/
theorem lemma_3_18 :
    ∃ search : LHS → SH → Disj, Computable₂ search ∧
      ∀ (Δ : LHS) (H : SH), Derives Δ (search Δ H) H := by sorry

end BiAbduction.Systematic
