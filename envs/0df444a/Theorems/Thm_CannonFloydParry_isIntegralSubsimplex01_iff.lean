-- Prove2me | Theorems.Thm_CannonFloydParry_isIntegralSubsimplex01_iff
-- name    : CannonFloydParry.isIntegralSubsimplex01_iff
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-26T20:07:35.248144+00:00
-- url     : https://prove2.me/theorems/6787f789-b173-43a7-8fc0-3fd4769c5b3e
-- title:
--   p. 251 — [a/b, c/d] is an integral subsimplex (in lowest terms, increasing) iff ad − bc = −1
-- statement:
--   Let $a \ge 0$ and $b, c, d > 0$ be integers with $a \le b$ and $c \le d$. Then the following are equivalent: $\gcd(a,b) = 1 = \gcd(c,d)$, $a/b < c/d$ and $[a/b, c/d]$ is an integral subsimplex of $[0,1]$; and $ad - bc = -1$.
--
--   **Formalization Note.** The source's sentence "Then $\gcd(a, b) = 1 = \gcd(c, d)$, $\frac ab < \frac cd$, and $[\frac ab, \frac cd]$ is an integral subsimplex of $[0,1]$ if and only if $ad - bc = -1$" is read with all three conditions on the left of the equivalence; the gcd conditions are needed there, since $[0/2, 1/1] = [0,1]$ is integral while $0 \cdot 1 - 2 \cdot 1 = -2$.
-- source:
--   Cannon, J. W., Floyd, W. J., Parry, W. R., Introductory notes on Richard Thompson's groups, L'Enseignement Mathématique (2) 42 (1996) 215–256, https://doi.org/10.5169/seals-87877, section 7, p. 251, integral subsimplices of [0,1]

import Mathlib
import Definitions.Def_CannonFloydParry_PIP

namespace CannonFloydParry

theorem isIntegralSubsimplex01_iff {a b c d : ℕ} (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hab : a ≤ b) (hcd : c ≤ d) :
    (Nat.gcd a b = 1 ∧ Nat.gcd c d = 1 ∧ (a : ℝ) / b < (c : ℝ) / d ∧
        IsIntegralSubsimplex01 ((a : ℝ) / b) ((c : ℝ) / d)) ↔
      (a : ℤ) * d - (b : ℤ) * c = -1 := by
  sorry

end CannonFloydParry
