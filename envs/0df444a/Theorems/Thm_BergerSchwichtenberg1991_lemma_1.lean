-- Prove2me | Theorems.Thm_BergerSchwichtenberg1991_lemma_1
-- name    : BergerSchwichtenberg1991.lemma_1
-- status  : Open
-- author  : @kmehltretter82
-- created : 2026-10-30T01:55:24.261384+00:00
-- url     : https://prove2.me/theorems/c8b8f03b-7913-403f-b349-4daf6b82845b
-- title:
--   Lemma 1: Bound-Variable Standardization Properties
-- statement:
--   Proves the four standardization properties of `α_k` (`EMB`) on p. 204: (1) `r =_α s → α_k(r) = α_k(s)`, (2) `α_k(r) =_α r`, (3) `α_k(r[s/x]) = (α_{k*0} r)[s/x]` when no index free in `s` extends `k*0`, and (4) `α_k(α_l(r)) = α_k(r)` when no index free in `r` extends `l`.
-- source:
--   Ulrich Berger and Helmut Schwichtenberg, 'An inverse of the evaluation functional for typed λ-calculus', Proceedings of the Sixth Annual IEEE Symposium on Logic in Computer Science (LICS 1991), pp. 203-211 (doi:10.1109/LICS.1991.151645). Lemma 1, p. 204.

import Definitions.Def_BergerSchwichtenberg1991_Syntax

namespace BergerSchwichtenberg1991

theorem lemma_1 (k : Index) :
    (∀ r s : Term, AlphaEq r s → alphaRename k r = alphaRename k s) ∧
    (∀ r : Term, (∀ m ∈ freeIndices r, ¬ IsPrefixOf k m) → AlphaEq (alphaRename k r) r) := by sorry

end BergerSchwichtenberg1991
