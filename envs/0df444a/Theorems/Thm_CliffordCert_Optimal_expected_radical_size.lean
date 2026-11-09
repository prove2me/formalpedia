-- Prove2me | Theorems.Thm_CliffordCert_Optimal_expected_radical_size
-- name    : CliffordCert.Optimal.expected_radical_size
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:34:31.936201+00:00
-- url     : https://prove2.me/theorems/033bffd7-4131-4bf8-bcfc-3a0d2ff51efc
-- title:
--   Lemma 8 — expected radical cardinality
-- statement:
--   Let $B$ be a nondegenerate alternating form on an $N$-dimensional binary vector space, with $N\ge2$, and let $1\le k\le N$. A uniformly selected $k$-subspace $W$ satisfies
--   $$\mathbb E|\operatorname{rad}(W)|=1+\frac{(2^k-1)(2^{N-k}-1)}{2^{N-1}-1}<3.$$
--   The expectation is of the number of radical vectors, not its dimension. This controls the average cost of repairing a uniformly positioned subspace.
--
--   Differences from the source:
--   - encoding: an arbitrary N-dimensional binary vector space → Fin N → ZMod 2 with an arbitrary alternating nondegenerate bilinear form when needed; reason: choosing coordinates is a linear isomorphism and changes no instance
--   - encoding: uniform expectation over all k-subspaces → the finite sum divided by the Grassmannian cardinality, with its nonemptiness asserted; reason: this is the uniform law and its denominator is nonzero
-- source:
--   Hyunho Cha, Jungwoo Lee, STOC 2027 submission #226 (October 2026), p. 13, Lemma 8, Eq. (22) (PDF p. 14); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/226.pdf

import Definitions.Def_CliffordCert_Optimal_symplectic
set_option autoImplicit false
noncomputable section
open scoped BigOperators ENNReal

namespace CliffordCert.Optimal
attribute [local instance] Classical.propDecidable Classical.decEq

theorem expected_radical_size {N : ℕ} (B : Form N) (hB : IsSymplectic B)
    (hN : 2 ≤ N) (k : ℕ) (hk : 1 ≤ k) (hkN : k ≤ N) :
    (grassmannian N k).Nonempty ∧
    expectedRadical B k = 1 + (((2 : ℝ)^k - 1) * ((2 : ℝ)^(N-k) - 1)) /
      ((2 : ℝ)^(N-1) - 1) ∧ expectedRadical B k < 3 := by sorry
end CliffordCert.Optimal
