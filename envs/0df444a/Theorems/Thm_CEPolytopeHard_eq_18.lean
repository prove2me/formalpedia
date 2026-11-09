-- Prove2me | Theorems.Thm_CEPolytopeHard_eq_18
-- name    : CEPolytopeHard.eq_18
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T17:15:30.017637+00:00
-- url     : https://prove2.me/theorems/5b6c31ea-84bf-46dc-98a6-d0ab820f985f
-- title:
--   Parameter choice (18) — $\rho \le \rho_0$ and $\eta < \zeta$
-- statement:
--   Let $q \ge 1$ be an integer and $0 < \zeta \le 1$. Set
--   $$
--   M = \lceil 64(3q+1)^2/\zeta^2\rceil, \qquad \rho_0 = \frac{\zeta}{32(q+1)M}, \qquad \epsilon = 2^{-\lceil \log_2(4/\rho_0^2)\rceil}, \tag{18}
--   $$
--   let $m$ be a positive integer with $4^{-(m+1)} \le \rho_0^2/4$ and $\rho = \sqrt{\epsilon + 4^{-(m+1)}}$. Then $\rho \le \rho_0$,
--   $$
--   2(1+qM)\rho \le \frac{\zeta}{16}\cdot\frac{1+qM}{(q+1)M} \le \frac\zeta{16}, \qquad (2q+1)\rho \le \frac{(2q+1)\zeta}{32(q+1)M} \le \frac1M,
--   $$
--   $$
--   3q\sqrt{M^{-1} + (2q+1)\rho} \le 3q\sqrt{\frac2M} \le \frac{\sqrt2\,\zeta}8\cdot\frac{3q}{3q+1} \le \frac{\sqrt2\,\zeta}{8},
--   $$
--   and therefore $\eta = 2(1+qM)\rho + 3q\sqrt{M^{-1} + (2q+1)\rho} < \zeta$.
--
--   With $\zeta$ from (12), the correlated equilibria of the constructed game at accuracy $\epsilon$ yield $\zeta$-convex EFPs of the lift.
--
--   Differences from the source:
--   - generalization: the least positive m with 4^{−(m+1)} ≤ ρ₀²/4 → any positive m with this inequality; reason: the conclusions use only the inequality; the least such m is one of them
--   - encoding: M, ρ₀, ϵ, ρ as defined values; ⌈·⌉, log₂ → real variables pinned by equations; Nat.ceil for M, Int.ceil in the exponent of ϵ, Real.logb 2; reason: names for the paper's values; same instances
-- source:
--   Anagnostides–Daskalakis–Farina–Golowich–Sandholm–Zhang, The Complexity of Correlated Equilibria Beyond Normal-Form Games, arXiv:2605.17665 (held version of November 2, 2026, sha256 6aec500a…7820), Eq. (18) and "Choosing the parameters", p.25

import Mathlib

set_option autoImplicit false

namespace CEPolytopeHard

/-- **The parameter choice (18)** (Anagnostides–Daskalakis–Farina–Golowich–Sandholm–Zhang, *The Complexity of Correlated Equilibria Beyond Normal-Form Games*, arXiv:2605.17665, held version of November 2, 2026, sha256 6aec500a…7820, "Choosing the parameters", p.25: "M = ⌈64(3q + 1)²/ζ²⌉,
ρ₀ = ζ/(32(q + 1)M), ϵ = 2^{−⌈log₂(4/ρ₀²)⌉}, (18) and choose the least positive m such that
4^{−(m+1)} ≤ ρ₀²/4. The choice of ϵ guarantees that ρ ≤ ρ₀. The first term in (15) satisfies
2(1 + qM)ρ ≤ (ζ/16)(1 + qM)/((q + 1)M) ≤ ζ/16, … (2q + 1)ρ ≤ (2q + 1)ζ/(32(q + 1)M) ≤ 1/M, so
3q√(M^{−1} + (2q + 1)ρ) ≤ 3q√(2/M) ≤ (√2ζ/8)(3q/(3q + 1)) ≤ √2ζ/8. Thus, η < ζ").

For every integer `q ≥ 1` and `0 < ζ ≤ 1`, with `M`, `ρ₀`, `ϵ` as in (18), a positive integer `m`
with `4^{−(m+1)} ≤ ρ₀²/4` and `ρ = √(ϵ + 4^{−(m+1)})`, every inequality of the display holds, and
`η = 2(1 + qM)ρ + 3q√(M^{−1} + (2q + 1)ρ) < ζ`.

**Formalization Note** `M, ρ₀, ϵ, ρ` are variables pinned to the printed values by equations;
`⌈·⌉` is `Nat.ceil` for `M` and `Int.ceil` for the exponent of `ϵ`, and `log₂ = Real.logb 2`. The
paper picks the least such `m`; every positive `m` with the inequality is allowed here. -/
theorem eq_18 (q : ℕ) (hq : 1 ≤ q) (ζ : ℝ) (hζ0 : 0 < ζ) (hζ1 : ζ ≤ 1) (M ρ₀ ε ρ : ℝ)
    (hM : M = (⌈64 * (3 * (q : ℝ) + 1) ^ 2 / ζ ^ 2⌉₊ : ℝ))
    (hρ₀ : ρ₀ = ζ / (32 * ((q : ℝ) + 1) * M))
    (hε : ε = (2 : ℝ) ^ (-⌈Real.logb 2 (4 / ρ₀ ^ 2)⌉))
    (m : ℕ) (hm0 : 0 < m) (hm : (4 : ℝ) ^ (-((m : ℤ) + 1)) ≤ ρ₀ ^ 2 / 4)
    (hρ : ρ = Real.sqrt (ε + (4 : ℝ) ^ (-((m : ℤ) + 1)))) :
    ρ ≤ ρ₀ ∧
    2 * (1 + q * M) * ρ ≤ ζ / 16 * ((1 + q * M) / ((q + 1) * M)) ∧
    ζ / 16 * ((1 + q * M) / ((q + 1) * M)) ≤ ζ / 16 ∧
    (2 * q + 1) * ρ ≤ (2 * q + 1) * ζ / (32 * (q + 1) * M) ∧
    (2 * q + 1) * ζ / (32 * (q + 1) * M) ≤ 1 / M ∧
    3 * q * Real.sqrt (M⁻¹ + (2 * q + 1) * ρ) ≤ 3 * q * Real.sqrt (2 / M) ∧
    3 * q * Real.sqrt (2 / M) ≤ Real.sqrt 2 * ζ / 8 * (3 * q / (3 * q + 1)) ∧
    Real.sqrt 2 * ζ / 8 * (3 * q / (3 * q + 1)) ≤ Real.sqrt 2 * ζ / 8 ∧
    2 * (1 + q * M) * ρ + 3 * q * Real.sqrt (M⁻¹ + (2 * q + 1) * ρ) < ζ := by sorry

end CEPolytopeHard
