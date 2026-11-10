-- Prove2me | Theorems.Thm_BMPV1173_Verification_theorem_1_1
-- name    : BMPV1173.Verification.theorem_1_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T23:04:14.99597+00:00
-- url     : https://prove2.me/theorems/ac87d303-53c7-4d3e-a928-3ab7cda2c08a
-- title:
--   Theorem 1.1 — full seventeen-twelfths BMPV upper bound
-- statement:
--   For every positive dimension $n$, the input consists of three arbitrary Boolean $n\times n$ matrices $A,B,C$. Boolean Matrix Product Verification accepts exactly when every entry of the OR-of-AND product $A\mathbin\bullet B$ equals the corresponding entry of $C$. There is a bounded-error quantum entry-query algorithm with
--   $$Q(\mathrm{BMPV}_n)=\widetilde O(n^{17/12}).$$
--   More precisely, there are absolute $C_0>0$, $k\in\mathbb N$ and a threshold $N$ such that, for every $n\ge\max(1,N)$, one circuit chosen before its unknown input uses at most $C_0n^{17/12}(1+\log n)^k$ bit queries and succeeds with probability at least $2/3$ on every triple. Smaller positive dimensions remain the same problem and may be handled by exhaustive queries. No promise on the matrices, acquired good event, correctness assumption, or assumed query bound is imposed on the input.
--
--   Differences from the source:
--   - encoding: bit entries indexed by [n] → Boolean functions on Fin n, with a matrix selector when needed; reason: the index bijection preserves every bit and every input instance
--   - encoding: soft-O query count and bounded error → global positive coefficient, natural logarithmic exponent and threshold, followed by one fixed-count XOR circuit per dimension with error at most 1/3; reason: only powers of log n are suppressed, the exponent is real, and the circuit is selected before its unknown input
-- source:
--   Amin Shiraz Gilani, François Le Gall, Xingyu Zhou, STOC 2027 submission #1173 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1173.pdf, Theorem 1.1, printed p.3 = PDF p.3.

import Definitions.Def_BMPV1173_Verification_QueryComplexity

namespace BMPV1173.Verification

/-- Gilani–Le Gall–Zhou, STOC 2027 submission #1173 (October 2026),
theorem 1 1, printed/PDF p.3. No promise on the unknown input. -/
theorem theorem_1_1 :
    SoftDecisionBound VerificationIndex (fun _ => Set.univ) (fun _ => bmpv) (17 / 12 : ℝ) := by sorry

end BMPV1173.Verification
