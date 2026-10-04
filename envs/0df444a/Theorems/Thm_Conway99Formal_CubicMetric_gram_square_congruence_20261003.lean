-- Prove2me | Theorems.Thm_Conway99Formal_CubicMetric_gram_square_congruence_20261003
-- name    : Conway99Formal.CubicMetric.gram_square_congruence_20261003
-- status  : Proved
-- author  : @harry
-- created : 2026-10-04T03:21:06.552825+00:00
-- url     : https://prove2.me/theorems/810a9f52-4dd3-465d-a565-21bc23b99efd
-- title:
--   Integral Gram-square congruence modulo four
-- statement:
--   Let $s$ be a finite set, let $G$ be an integer matrix indexed by a type containing $s$, and let $a$ assign an integer coefficient to each index. Suppose $G$ is symmetric and every diagonal entry is $4$. Then the quadratic form obtained by replacing each entry $G_{ij}$ with $G_{ij}^2-G_{ij}$ is divisible by four:
--
--   $$
--   4 \mid \sum_{i\in s}\sum_{j\in s} a_i(G_{ij}^2-G_{ij})a_j.
--   $$
--
--   This abstract congruence applies to any integral norm-four Gram matrix. Instantiating it for a particular graph or lattice requires separately proving that the actual Gram matrix is integral, symmetric, and has diagonal four.
-- source:
--   Conway99 cubic-metric formalization, GramParity.lean, theorem Conway99Formal.CubicMetric.gram_square_congruence; source bundle frozen at integration commit a45708acebe3f397faccb1b646be906f24f23ee5, originally formalized from GC8 §1 (gram_congruence_turn8.md) and CTF §3 (CUBIC_TRACE_FORM.md). This submission states only the standalone arithmetic lemma, not its graph/lattice application.

import Mathlib
set_option autoImplicit false

theorem Conway99Formal.CubicMetric.gram_square_congruence_20261003 {ι : Type*} [DecidableEq ι] (s : Finset ι) (G : ι → ι → ℤ) (a : ι → ℤ) (hsym : ∀ i j, G i j = G j i) (hdiag : ∀ i, G i i = 4) : 4 ∣ ∑ i ∈ s, ∑ j ∈ s, a i * ((G i j) ^ 2 - G i j) * a j := by sorry
