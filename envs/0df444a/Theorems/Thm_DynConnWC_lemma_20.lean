-- Prove2me | Theorems.Thm_DynConnWC_lemma_20
-- name    : DynConnWC.lemma_20
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:32:18.605194+00:00
-- url     : https://prove2.me/theorems/de1b7cc0-ed24-49af-965d-8c9f460adaf5
-- title:
--   Lemma 20 — at most $2^{D(F)}$ cuts of unions of trees
-- statement:
--   Let $F\subseteq G$ be a forest. Then $D(F)\ge0$, and there are at most $2^{D(F)}$ distinct edge sets of the form $\delta_G(S)$, where $S$ is a union of trees of $F$ (the empty union included).
--
--   The final cutset instances need to succeed only on these cuts, however the final forest was formed.
--
--   Differences from the source:
--   - encoding: exponent $D(F)$ → `(deficit G F).toNat`, together with $0\le D(F)$; reason: the deficit is an integer, and it is nonnegative because $F\subseteq G$
-- source:
--   King, Liu, Nie, Fully Dynamic Connectivity in O(log³ n) Worst-Case Update Time (STOC 2027 submission, preprint, sha256 9d16c13e96cde8418fd8fd9bbadff18443fe432ac60bdd3db036eb8f02635770), Lemma 20, p.21 (PDF 22); Definition 2, p.3–4

import Mathlib
import Definitions.Def_DynConnWC_Forest

set_option autoImplicit false

namespace DynConnWC

open Classical in
/-- **Lemma 20 (Few possible cuts).** King, Liu, Nie, *Fully Dynamic Connectivity in O(log³ n) Worst-Case Update Time* (STOC 2027 submission, sha256 9d16c13e…), p.21 (PDF 22).
"Let F ⊆ G be a forest. There are at most 2^{D(F)} distinct edge sets of the form δ_G(S), where S is a
union of trees of F."

**Formalization Note.** `D(F) ≥ 0` because `F ⊆ G`, so the exponent `(deficit G F).toNat` is exact. The
empty union is one of the unions. -/
theorem lemma_20 {n : ℕ} (G : SimpleGraph (Fin n)) (F : Finset (Sym2 (Fin n))) (hF : IsForestSet F)
    (hsub : SubG F G) :
    0 ≤ deficit G F ∧ ((unionsOfTrees F).image (cutset G)).card ≤ 2 ^ (deficit G F).toNat := by sorry

end DynConnWC
