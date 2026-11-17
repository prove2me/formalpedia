-- Prove2me | Theorems.Thm_ECDLP_P_order
-- name    : ECDLP.P_order
-- status  : Open
-- author  : @Lucas
-- created : 2026-11-16T23:44:17.163212+00:00
-- url     : https://prove2.me/theorems/8acc5a91-73c7-4183-b9d5-6659eb9d3992
-- title:
--   The challenge base point has order $n$
-- statement:
--   The challenge base point $P \in E(\mathbb{F}_p)$ has additive order exactly $n$:
--
--   $$\operatorname{ord}(P) = n = 18406372847737621097080107628624365276513063062857122317960690589425712086189.$$
--
--   The benchmark asserts that $P$ is a point of large prime order $n$; this theorem certifies that assertion, so the subgroup $\langle P\rangle$ has exactly $n$ elements and the discrete logarithm in it is well defined modulo $n$.
--
--   **Formalization Note.** `addOrderOf` is Mathlib's order of an element of an additive group; the group law on `ECDLP.E.toAffine.Point` requires the `Fact (Nat.Prime ECDLP.p)` instance, which is the theorem's only hypothesis.
-- source:
--   Epoch AI, FrontierMath: Open Problems — The Elliptic-Curve Discrete Logarithm Problem (ECDLP), https://epoch.ai/frontiermath/open-problems/elliptic-curve-discrete-logarithm — public challenge data (p, a, b, P, Q, n, h) and Task section.

import Mathlib
import Definitions.Def_ECDLPChallengeData

namespace ECDLP

theorem P_order [Fact (Nat.Prime ECDLP.p)] : addOrderOf ECDLP.P = ECDLP.n := by sorry

end ECDLP
