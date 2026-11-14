-- Prove2me | Theorems.Thm_CatalyticTreeEval_Main_canonical_indexing_matching
-- name    : CatalyticTreeEval.Main.canonical_indexing_matching
-- status  : Proved
-- author  : @sragavan
-- created : 2026-11-14T02:35:40.842563+00:00
-- url     : https://prove2.me/theorems/500f0fbc-30a0-4b42-82aa-59ebe52e5903
-- title:
--   Canonical coefficient and evaluation vectors form a matching family
-- statement:
--   Let $p_i$ be distinct primes, $m=\prod_i p_i$, and let $w<\prod_i p_i^{e_i}$. For any actual injective subset and square-free monomial indexings, the coefficient vectors of the restricted CRT detector and the corresponding Boolean evaluation vectors form an $S$-matching family, where $S$ is the canonical zero-or-one residue set. The label count is $\binom Hw$ and the dimension is $\sum_{j<\Delta}\binom Hj$, with $\Delta=\max_i p_i^{e_i}$.
--
--   The inner product is detector evaluation at the intersection of the indexed subsets. This is the algebraic content of Lemma B.1 for explicitly indexed coordinate functions; uniform native access is separate.
-- source:
--   Henzinger, Pyne and Ragavan, Catalytic Tree Evaluation from Matching Vectors, https://arxiv.org/html/2602.14320v3, Appendix B, Lemma B.1.

import Definitions.Def_CatalyticTreeEval_CanonicalCoordinates

set_option autoImplicit false

namespace CatalyticTreeEval.Main

theorem canonical_indexing_matching {t : ℕ} (p e : Fin t → ℕ) (hp : PrimeData p)
    (w H : ℕ) (hw : w < ∏ i, p i ^ e i) (I : CanonicalIndexing H w (delta p e)) :
    SMatching (canonical p (modulus p))
      (canonicalCoefficientVectors p e hp w H I) (canonicalEvaluationVectors p e w H I) := by sorry

end CatalyticTreeEval.Main
