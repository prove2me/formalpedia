-- Prove2me | Theorems.Thm_EllipsoidFitting_claim_4_11
-- name    : EllipsoidFitting.claim_4_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:43:45.228629+00:00
-- url     : https://prove2.me/theorems/76a18361-ec13-41ec-8277-8bc7051f80c5
-- title:
--   Claim 4.11 — $|c_t(k)|\le\gamma^{-t/2}(2\sqrt\gamma)^k$
-- statement:
--   Let $0<\gamma\le1$ and let $c_t(k)$ be the coefficients of $(x-(1+\gamma))^k$ in the MP basis, defined by the recurrence of p.45. For all $k,t\ge0$,
--   $$
--   |c_t(k)|\le\gamma^{-t/2}\,(2\sqrt\gamma)^k.
--   $$
--
--   The bound feeds the trace-moment proof that $\|A-(1+\gamma)I\|\le(1+o(1))\,2\sqrt\gamma$ (Lemma 4.10). The printed "in particular, for $k=2q$" is the instance $k=2q$.
--
--   Differences from the source: none.
-- source:
--   de la Cerda, Potechin, Tulsiani, Xu, Sharp Phase Transition for Ellipsoid Fitting, arXiv:2608.12415 (version of Nov 3, 2026, sha256 e4268312ca36b47de9467896061e7747d1efb1efe9677b7f14bd1b0647e093bc), Claim 4.11, p.45 (PDF p.47)

import Mathlib
import Definitions.Def_EllipsoidFitting_mpCoeff

set_option autoImplicit false

namespace EllipsoidFitting

/-- **Claim 4.11 (coefficient bound in the MP basis).** de la Cerda, Potechin, Tulsiani, Xu,
*Sharp Phase Transition for Ellipsoid Fitting*, arXiv:2608.12415 (version of Nov 3, 2026),
Claim 4.11, p.45: "Assume 0 < γ ≤ 1. For every k ≥ 0 and every t ≥ 0, |ct(k)| ≤ γ^{−t/2}(2√γ)^k."

**Formalization Note** `c_t(k)` is `mpCoeff γ k t`, defined by the recurrence of p.45;
`γ^{−t/2}` is the real power `Real.rpow` (`γ > 0`). The "In particular, for k = 2q" line is an
instance and is not stated separately. -/
theorem claim_4_11 (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) (k t : ℕ) :
    |mpCoeff γ k t| ≤ γ ^ (-(t : ℝ) / 2) * (2 * Real.sqrt γ) ^ k := by sorry

end EllipsoidFitting
