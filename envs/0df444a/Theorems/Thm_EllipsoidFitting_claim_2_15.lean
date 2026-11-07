-- Prove2me | Theorems.Thm_EllipsoidFitting_claim_2_15
-- name    : EllipsoidFitting.claim_2_15
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:42:30.423204+00:00
-- url     : https://prove2.me/theorems/b353ff76-b80b-46cf-900a-cd5c5875f71b
-- title:
--   Claim 2.15 — $\frac1x=\frac1{1-\gamma}\sum_{t\ge0}(-1)^tq_t(x)$ on the MP support
-- statement:
--   Let $0<\gamma<1$ and $x\in[(1-\sqrt\gamma)^2,(1+\sqrt\gamma)^2]$, the Marchenko–Pastur support. Then the series below converges and
--   $$
--   \frac1x=\frac1{1-\gamma}\sum_{t\ge0}(-1)^t\,q_t^{(\gamma)}(x).
--   $$
--
--   Applied to the spectrum of $A$ this gives the inverse expansion $A^{-1}=\frac1{1-\gamma}\sum_{t\ge0}(-1)^tq_t(A)$ (eq. (6)).
--
--   **Formalization Note** Stated as `HasSum`, so convergence is part of the claim; both endpoints of the support are included.
--
--   Differences from the source:
--   - encoding: γ < 1 → 0 < γ < 1; reason: Definition 2.14's standing 'Fix 0 < γ < 1', under which q_t^{(γ)} is introduced
--   - encoding: 1/x equals an infinite sum → HasSum of the terms (1/(1−γ))(−1)^t q_t(x) with sum 1/x; reason: asserts convergence; a tsum would be 0 on a divergent series
-- source:
--   de la Cerda, Potechin, Tulsiani, Xu, Sharp Phase Transition for Ellipsoid Fitting, arXiv:2608.12415 (version of Nov 3, 2026, sha256 e4268312ca36b47de9467896061e7747d1efb1efe9677b7f14bd1b0647e093bc), Claim 2.15, p.18 (PDF p.20)

import Mathlib
import Definitions.Def_EllipsoidFitting_mpPoly

set_option autoImplicit false

namespace EllipsoidFitting

/-- **Claim 2.15 (`1/x` in the MP basis).** de la Cerda, Potechin, Tulsiani, Xu, *Sharp Phase
Transition for Ellipsoid Fitting*, arXiv:2608.12415 (version of Nov 3, 2026), Claim 2.15, p.18:
"For x ∈ [(1 − √γ)², (1 + √γ)²] in the Marchenko–Pastur support and γ < 1, 1/x = 1/(1−γ)
∑_{t≥0} (−1)^t qt(x)."

For `0 < γ < 1` and `x` in the Marchenko–Pastur support (edges included), the series
`∑_t (1/(1−γ)) (−1)^t q_t(x)` converges to `1/x`.

**Formalization Note** `0 < γ` is Definition 2.14's standing "Fix 0 < γ < 1". The series is a
`HasSum` (convergence is part of the claim; a `tsum` would be `0` on a divergent series). -/
theorem claim_2_15 (γ x : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (hx : x ∈ Set.Icc ((1 - Real.sqrt γ) ^ 2) ((1 + Real.sqrt γ) ^ 2)) :
    HasSum (fun t : ℕ => 1 / (1 - γ) * ((-1 : ℝ) ^ t * (mpPoly γ t).eval x)) (1 / x) := by sorry

end EllipsoidFitting
