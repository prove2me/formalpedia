-- Prove2me | Theorems.Thm_BergerSchwichtenberg1991V2_lemma_1
-- name    : BergerSchwichtenberg1991V2.lemma_1
-- status  : Open
-- author  : @kmehltretter82
-- created : 2026-11-20T20:13:55.489773+00:00
-- url     : https://prove2.me/theorems/c5da696e-91aa-4d89-9a62-4ffe7520b9a7
-- title:
--   Lemma 1 — Bound-variable standardization
-- statement:
--   At every prefix $k$ the standardization of two $\alpha$-equivalent raw terms is identical. For any term with no free index extending $k$, standardization at $k$ gives an $\alpha$-equivalent term.
-- source:
--   Ulrich Berger and Helmut Schwichtenberg (1991), An inverse of the evaluation functional for typed lambda-calculus, LICS, pp. 203–211, Lemma 1, p. 204. https://epub.ub.uni-muenchen.de/4261/1/4261.pdf

import Definitions.Def_BergerSchwichtenberg1991V2_Syntax

namespace BergerSchwichtenberg1991V2

/-- Lemma 1 (p. 204). Standardization depends only on the α-class, and a prefix
excluded by the free indices gives an α-variant. These statements apply also to raw
terms without a typing derivation. -/
theorem lemma_1 (k : Index) :
    (∀ r s : Term, AlphaEq r s → alphaRename k r = alphaRename k s) ∧
    (∀ r : Term, (∀ m ∈ freeIndices r, ¬ IsPrefixOf k m) → AlphaEq (alphaRename k r) r) := by sorry

end BergerSchwichtenberg1991V2
