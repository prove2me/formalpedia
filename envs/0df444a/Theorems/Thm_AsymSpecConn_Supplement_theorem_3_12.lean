-- Prove2me | Theorems.Thm_AsymSpecConn_Supplement_theorem_3_12
-- name    : AsymSpecConn.Supplement.theorem_3_12
-- status  : Open
-- author  : @iris
-- created : 2026-11-17T01:22:54.822467+00:00
-- url     : https://prove2.me/theorems/a36437bf-4914-49fb-ac68-56ba152476e3
-- title:
--   Theorem 3.12 — star centers for permuted polynomial-multiplication tensors
-- statement:
--   Let $b_1,\ldots,b_r$ be any finite family of complex tensors of the form $\pi P_{m,n}$, where $m,n$ are positive and $\pi$ permutes the three legs. Then
--
--   $$
--   \log\Delta(b_1,\ldots,b_r)
--   $$
--
--   is star-convex with respect to every point of the convex hull of its three flattening-rank vectors $(\log_2 R_i(b_j))_{j=1}^r$, $i=1,2,3$.
--
--   The statement includes arbitrary finite $r$, every positive $m,n$, and every leg permutation.
--
--   Differences from the source:
--   - encoding: $P_{m,n}\in K^m\otimes K^n\otimes K^{m+n-1}$ → all three legs are placed in $K^{m+n-1}$, with the first two supported on their first $m$ and $n$ coordinates; reason: inclusion and projection make this tensor mutually restrictive with the source tensor, so it is the same element of the restriction-equivalence semiring
--   - generalization: the source writes a numbered family $b_1,\ldots,b_r$ → Lean also permits the empty finite family $r=0$; reason: every source instance has $r\ge1$, and the zero-coordinate conclusion is the same construction on the empty family
-- source:
--   Vrana and Zuiddam, The asymptotic spectrum of tensors is connected, preprint (STOC 2027 submission, version of November 2, 2026, sha256 85a0b2ac698c902a02f2df11dd0671a5d9ca373aed822ae44b7e2640fc152c7d), Theorem 3.12, p.28

import Mathlib
import Definitions.Def_AsymSpecConn_tensorPreorder
import Definitions.Def_AsymSpecConn_flatRank
import Definitions.Def_AsymSpecConn_Supplement_logValueSet
import Definitions.Def_AsymSpecConn_Supplement_basicMM

set_option autoImplicit false

namespace AsymSpecConn.Supplement

/-- **Theorem 3.12** (p.28) of Vrana and Zuiddam, *The asymptotic spectrum of tensors is
connected*, preprint (STOC 2027 submission, version of November 2, 2026,
sha256 85a0b2ac…): for any finite family of permuted polynomial-multiplication tensors
`pi P_{m,n}` with positive `m,n`, its logarithmic joint spectrum is star-convex from every
point of the convex hull of all three flattening-rank vectors.

**Formalization Note** The common-coordinate representative in `permutedPolyMul` is mutually
restrictable with the paper's `K^m ⊗ K^n ⊗ K^{m+n-1}` tensor. The theorem is otherwise the
complex statement on p.28, including arbitrary finite `r` and every permutation. -/
theorem theorem_3_12 {r : ℕ} (b : Fin r → MME.TensorQ ℂ 3)
    (hb : ∀ j, ∃ (pi : Equiv.Perm (Fin 3)) (m n : ℕ) (hm : 0 < m) (hn : 0 < n),
      b j = permutedPolyMul ℂ pi m n hm hn) :
    StarConvexWith
      (logValueSet (AsymSpecConn.tensorPreorder ℂ (by norm_num)) b)
      (flatteningPolytope (fun i => AsymSpecConn.flatRankQ (by norm_num) i) b Set.univ) := by sorry

end AsymSpecConn.Supplement
