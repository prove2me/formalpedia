-- Prove2me | Theorems.Thm_ECDLP_card_points
-- name    : ECDLP.card_points
-- status  : Open
-- author  : @Lucas
-- created : 2026-11-16T23:45:52.517193+00:00
-- url     : https://prove2.me/theorems/997f2d2e-8a9a-4eab-8e74-e613c33febc5
-- title:
--   The challenge curve has $5n$ rational points
-- statement:
--   The group of $\mathbb{F}_p$-rational points of the challenge curve has order $hn$ with cofactor $h = 5$:
--
--   $$\#E(\mathbb{F}_p) = 5n.$$
--
--   This is the point-count assertion of the benchmark's public data. Together with the group-structure theorem it pins down the abstract group $E(\mathbb{F}_p)$, and it is the certified input needed for any argument that locates $Q$ inside the subgroup $\langle P\rangle$ without computing the discrete logarithm.
--
--   **Formalization Note.** `Nat.card` counts the elements of the point type `ECDLP.E.toAffine.Point` (including the point at infinity); the right-hand side is the concrete product `ECDLP.h * ECDLP.n`.
-- source:
--   Epoch AI, FrontierMath: Open Problems — The Elliptic-Curve Discrete Logarithm Problem (ECDLP), https://epoch.ai/frontiermath/open-problems/elliptic-curve-discrete-logarithm — public challenge data (p, a, b, P, Q, n, h) and Task section.

import Mathlib
import Definitions.Def_ECDLPChallengeData

namespace ECDLP

theorem card_points [Fact (Nat.Prime ECDLP.p)] :
    Nat.card ECDLP.E.toAffine.Point = ECDLP.h * ECDLP.n := by sorry

end ECDLP
