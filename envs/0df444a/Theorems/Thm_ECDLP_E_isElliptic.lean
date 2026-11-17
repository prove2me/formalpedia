-- Prove2me | Theorems.Thm_ECDLP_E_isElliptic
-- name    : ECDLP.E_isElliptic
-- status  : Proved
-- author  : @Lucas
-- created : 2026-11-16T23:43:53.561369+00:00
-- url     : https://prove2.me/theorems/7f74b2c6-9349-4677-bb77-1464a384ff05
-- title:
--   The challenge curve is nonsingular
-- statement:
--   The challenge curve $E : y^2 = x^3 + ax + b$ over $\mathbb{F}_p$ is an elliptic curve: its discriminant is nonzero, equivalently
--
--   $$4a^3 + 27b^2 \ne 0 \quad \text{in } \mathbb{F}_p.$$
--
--   This certifies the nonsingularity implicit in the benchmark's setup, where $E$ is presented as an elliptic curve.
--
--   **Formalization Note.** `WeierstrassCurve.IsElliptic` is Mathlib's typeclass asserting that the discriminant `Δ` is a unit; over the field $\mathbb{F}_p$ this is equivalent to $\Delta \ne 0$, and for a short Weierstrass equation to $4a^3 + 27b^2 \ne 0$.
-- source:
--   Epoch AI, FrontierMath: Open Problems — The Elliptic-Curve Discrete Logarithm Problem (ECDLP), https://epoch.ai/frontiermath/open-problems/elliptic-curve-discrete-logarithm — public challenge data (p, a, b, P, Q, n, h) and Task section.

import Mathlib
import Definitions.Def_ECDLPChallengeData

namespace ECDLP

theorem E_isElliptic : ECDLP.E.IsElliptic := by sorry

end ECDLP
