-- Prove2me | Theorems.Thm_BMPV1173_Verification_proposition_3_1
-- name    : BMPV1173.Verification.proposition_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T23:05:05.560139+00:00
-- url     : https://prove2.me/theorems/06a7bdcc-47c7-47d4-8e8d-6d409f6324bf
-- title:
--   Proposition 3.1 — both triangle reductions and the triangle bound
-- statement:
--   The complement of $\mathrm{BMPV}^{\le}_n$ reduces to triangle detection on $3n$ vertices, and triangle detection on $n$ vertices reduces to the complement of $\mathrm{BMPV}^{\le}_n$. The explicit maps answer each target bit by a constant or one possibly complemented source bit. They retain both predicate identities and the full chain
--   $$Q(\mathrm{Triangle}_n)\le Q(\mathrm{BMPV}^{\le}_n)\le Q(\mathrm{Triangle}_{3n})=O(n^{5/4}).$$
--   Graphs are simple and undirected, with fixed zero diagonal and symmetric adjacency input. The final upper bound is log-free and is part of the conclusion, rather than an assumed triangle algorithm. The complement in the graph-to-verification claimed matrix is essential.
--
--   Differences from the source:
--   - encoding: bit entries indexed by [n] → Boolean functions on Fin n, with a matrix selector when needed; reason: the index bijection preserves every bit and every input instance
--   - encoding: constant-query oracle reductions and the full complexity chain → explicit constant-or-one-entry bit maps, their Boolean predicate identities, exact ENat complexity inequalities, and an existential log-free triangle circuit bound; reason: the maps preserve the source oracle convention, ENat retains an empty feasible set as top, and the final upper bound is asserted at full strength
-- source:
--   Amin Shiraz Gilani, François Le Gall, Xingyu Zhou, STOC 2027 submission #1173 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1173.pdf, Proposition 3.1, printed p.17 = PDF p.17.

import Definitions.Def_BMPV1173_Verification_Reductions

namespace BMPV1173.Verification

/-- Both source maps and their predicate identities, both exact query inequalities,
and the log-free O(n^(5/4)) triangle upper bound of Proposition 3.1, p.17. -/
theorem proposition_3_1 :
    (∀ (n : ℕ) (hn : 0 < n),
      (∀ x : VerificationInput n,
        SimpleGraphInput (evalMap (verificationTriangleMap n hn) x) ∧
        triangle (evalMap (verificationTriangleMap n hn) x) = !(bmpvLE x)) ∧
      (∀ x : MatrixIndex n → Bool, SimpleGraphInput x →
        bmpvLE (evalMap (triangleVerificationMap n) x) = !(triangle x)) ∧
      qTriangle n ≤ qBMPVLE n ∧ qBMPVLE n ≤ qTriangle (3*n)) ∧
    ∃ (C : ℝ) (N : ℕ), 0 < C ∧ ∀ n : ℕ, max 1 N ≤ n →
      ∃ T : ℕ, HasDecision {x | SimpleGraphInput x} (@triangle (3*n)) (1/3) T ∧
        (T : ℝ) ≤ C*(n : ℝ)^(5/4 : ℝ) := by sorry

end BMPV1173.Verification
