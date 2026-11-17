-- Prove2me | Theorems.Thm_AsymSpecConn_Supplement_theorem_4_1
-- name    : AsymSpecConn.Supplement.theorem_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-17T01:26:42.730482+00:00
-- url     : https://prove2.me/theorems/f00e5253-f217-4700-83c8-f8d645ffb3ca
-- title:
--   Theorem 4.1 — irreducible tensor monomials yield a flattening-rank center polytope
-- statement:
--   Let $K$ be any field, let $b_1,\ldots,b_r$ be nonzero $k$-tensors, and let $I\subseteq[k]$. Suppose that for every $i\in I$ and every multi-index $u\in\mathbb N^r$, including $u=0$, the tensor monomial $b^u=\prod_j b_j^{u_j}$ is $i$-irreducible. Then $\log\Delta_K(b_1,\ldots,b_r)$ is star-convex with respect to every point of
--
--   $$
--   \operatorname{conv}\bigl\{(\log_2 R_i(b_j))_{j=1}^r:i\in I\bigr\}.
--   $$
--
--   No restriction is placed on the characteristic or algebraic closure of $K$.
--
--   Differences from the source: none.
-- source:
--   Vrana and Zuiddam, The asymptotic spectrum of tensors is connected, preprint (STOC 2027 submission, version of November 2, 2026, sha256 85a0b2ac698c902a02f2df11dd0671a5d9ca373aed822ae44b7e2640fc152c7d), Theorem 4.1, p.30

import Mathlib
import Definitions.Def_AsymSpecConn_tensorPreorder
import Definitions.Def_AsymSpecConn_flatRank
import Definitions.Def_AsymSpecConn_Supplement_logValueSet
import Definitions.Def_AsymSpecConn_Supplement_basicMM

set_option autoImplicit false

namespace AsymSpecConn.Supplement

universe u

/-- **Theorem 4.1** (p.30) of Vrana and Zuiddam, *The asymptotic spectrum of tensors is
connected*, preprint (STOC 2027 submission, version of November 2, 2026,
sha256 85a0b2ac…). Over an arbitrary field, if every tensor monomial `b^u` is
`i`-irreducible for every selected leg `i`, then the logarithmic joint spectrum is star-convex
from every point of the corresponding flattening-rank polytope.

**Formalization Note** The quantifier over `u : Fin r → ℕ` includes the zero multi-index,
exactly as `u ∈ ℕ^r` in the source. No characteristic or algebraic-closure condition is added. -/
theorem theorem_4_1 (K : Type u) [Field K] {k : ℕ} (hk : 2 ≤ k) {r : ℕ}
    (b : Fin r → MME.TensorQ K k) (hb : ∀ j, b j ≠ 0) (I : Set (Fin k))
    (hirr : ∀ i ∈ I, ∀ v : Fin r → ℕ, FieldIrreducible hk i (tensorMonomial b v)) :
    StarConvexWith
      (logValueSet (AsymSpecConn.tensorPreorder K hk) b)
      (flatteningPolytope (fun i => AsymSpecConn.flatRankQ hk i) b I) := by sorry

end AsymSpecConn.Supplement
