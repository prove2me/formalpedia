-- Prove2me | Theorems.Thm_BorelNormality_rational_not_normal
-- name    : BorelNormality.rational_not_normal
-- status  : Proved
-- author  : @LG
-- created : 2026-11-18T17:09:17.892004+00:00
-- url     : https://prove2.me/theorems/a2ba188e-6a7a-4d97-83e6-1e4e4eb47af9
-- title:
--   No rational number is normal in any base
-- statement:
--   No rational number is normal in any integer base. Let $q \in \mathbb{Q}$ and let $b \ge 2$ be an integer. Viewed as a real number, $q$ is **not** normal in base $b$:
--
--   $$\neg\,\mathrm{IsNormalReal}(b, q).$$
--
--   The base-$b$ expansion of a rational number is eventually periodic, so most blocks longer than the period never occur at all; their limiting frequency is $0$ rather than $b^{-k}$. This elementary fact delimits Borel's conjecture: among algebraic numbers, the rational ones are provably non-normal, which is why the conjecture assumes irrationality.
--
--   **Formalization Note.** $q$ is coerced to $\mathbb{R}$; `Normal.IsNormalReal` is the platform's base-$b$ normality predicate from `Normal_Core`, applied to the canonical fractional-part digits.
-- source:
--   https://en.wikipedia.org/wiki/Normal_number, section 'Non-normal numbers': 'No rational number is normal in any base, since the digit sequence of a rational number is eventually periodic, and thus most of the strings that are longer than the period do not appear in the digit sequence.' Eventual periodicity of rational expansions: B. Adamczewski, Y. Bugeaud, Ann. of Math. (2) 165 (2007), 547–565, Introduction (p. 547).

import Mathlib
import Definitions.Def_Normal_Core

set_option autoImplicit false

namespace BorelNormality

theorem rational_not_normal (q : ℚ) (b : ℕ) (hb : 2 ≤ b) :
    ¬ Normal.IsNormalReal b (q : ℝ) := by sorry

end BorelNormality
