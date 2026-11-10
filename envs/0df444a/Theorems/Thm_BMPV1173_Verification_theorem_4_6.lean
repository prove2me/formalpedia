-- Prove2me | Theorems.Thm_BMPV1173_Verification_theorem_4_6
-- name    : BMPV1173.Verification.theorem_4_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T23:04:10.059691+00:00
-- url     : https://prove2.me/theorems/66a6b79c-1932-4357-b626-e7c2c2d3c458
-- title:
--   Theorem 4.6 — general single-list OV upper bound
-- statement:
--   For an arbitrary indexed list of $n$ Boolean vectors of dimension $n$, Orthogonal Vectors accepts exactly when two distinct indices have disjoint supports. There is a bounded-error entry-query algorithm with
--   $$Q(\mathrm{OV}_n)=\widetilde O(n^{17/12}).$$
--   The coefficient, logarithmic exponent and asymptotic threshold are absolute. For each dimension the algorithm is selected before the unknown list and succeeds with probability at least $2/3$ on every list. Equal vectors at distinct positions are allowed. No intersection, sparsity or size-class promise is assumed, and no preprocessing good event is a hypothesis.
--
--   Differences from the source:
--   - encoding: bit entries indexed by [n] → Boolean functions on Fin n, with a matrix selector when needed; reason: the index bijection preserves every bit and every input instance
--   - encoding: soft-O query count and bounded error → global positive coefficient, natural logarithmic exponent and threshold, followed by one fixed-count XOR circuit per dimension with error at most 1/3; reason: only powers of log n are suppressed, the exponent is real, and the circuit is selected before its unknown input
-- source:
--   Amin Shiraz Gilani, François Le Gall, Xingyu Zhou, STOC 2027 submission #1173 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1173.pdf, Theorem 4.6, printed p.27 = PDF p.27.

import Definitions.Def_BMPV1173_Verification_QueryComplexity

namespace BMPV1173.Verification

/-- Gilani–Le Gall–Zhou, STOC 2027 submission #1173 (October 2026),
theorem 4 6, printed/PDF p.27. No promise on the unknown input. -/
theorem theorem_4_6 :
    SoftDecisionBound MatrixIndex (fun _ => Set.univ) (fun _ => ov) (17 / 12 : ℝ) := by sorry

end BMPV1173.Verification
