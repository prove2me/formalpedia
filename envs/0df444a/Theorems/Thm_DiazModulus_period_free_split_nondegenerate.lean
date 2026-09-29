-- Prove2me | Theorems.Thm_DiazModulus_period_free_split_nondegenerate
-- name    : DiazModulus.period_free_split_nondegenerate
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-13T10:45:56.91148+00:00
-- url     : https://prove2.me/theorems/ecd1fff7-7029-4345-8318-1510b0fdb4f2
-- title:
--   Both halves of the period-free split are non-empty
-- statement:
--   `DiazModulus.diaz_of_exp_not_real_irrational_angle_period_free` concerns the $u$ with $u \neq 0$, $|u|$ algebraic, $\operatorname{Im} e^{u} \neq 0$, $u$ on neither axis, $\operatorname{Im} u \notin \mathbb{Q}\pi$, and no non-zero rational $r$ making $\pi(\operatorname{Im} u + r\pi)$ algebraic. Its two children split this set according to whether $\pi \operatorname{Im} u$ is algebraic. **Both parts are non-empty:**
--
--   - $w_C = \sqrt{16 - \pi^{-2}} + i/\pi$ has $|w_C| = 4$ and $\pi \operatorname{Im} w_C = 1$, algebraic;
--   - $w_B = \sqrt{15} + i$ has $|w_B| = 4$ and $\pi \operatorname{Im} w_B = \pi$, transcendental.
--
--   **Proof sketch.** Both points have modulus $4$ and lie off the axes. $\operatorname{Im} u \in \mathbb{Q}\pi$ would give $1 = q\pi^{2}$ or $1 = q\pi$, impossible as $\pi$ is transcendental, and then $\sin(\operatorname{Im} u) \neq 0$ gives $\operatorname{Im} e^{u} \neq 0$. For a non-zero rational $r$, $\pi(\operatorname{Im} u + r\pi)$ is $1 + r\pi^{2}$ or $\pi + r\pi^{2}$; either being algebraic would make $\pi$ algebraic.
--
--   **What it is for.** Neither child is vacuous, so the split is a genuine case division: a proof of either child has to handle actual points.
--
--   **Not claimed.** Nothing about the transcendence of $e^{u}$ at these points.
-- source:
--   Elementary; explicit witnesses. Uses DiazModulus.pi_transcendental (Proved on this mission).

import Mathlib
import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus
theorem period_free_split_nondegenerate :
    (∃ u : ℂ, u ≠ 0 ∧ IsAlgebraic ℚ ((‖u‖ : ℝ) : ℂ) ∧ (Complex.exp u).im ≠ 0 ∧
        ¬ (u.im = 0 ∨ u.re = 0) ∧ (¬ ∃ q : ℚ, u.im = (q : ℝ) * Real.pi) ∧
        (¬ ∃ r : ℚ, r ≠ 0 ∧
          IsAlgebraic ℚ ((Real.pi * (u.im + (r : ℝ) * Real.pi) : ℝ) : ℂ)) ∧
        IsAlgebraic ℚ ((Real.pi * u.im : ℝ) : ℂ)) ∧
    (∃ u : ℂ, u ≠ 0 ∧ IsAlgebraic ℚ ((‖u‖ : ℝ) : ℂ) ∧ (Complex.exp u).im ≠ 0 ∧
        ¬ (u.im = 0 ∨ u.re = 0) ∧ (¬ ∃ q : ℚ, u.im = (q : ℝ) * Real.pi) ∧
        (¬ ∃ r : ℚ, r ≠ 0 ∧
          IsAlgebraic ℚ ((Real.pi * (u.im + (r : ℝ) * Real.pi) : ℝ) : ℂ)) ∧
        Transcendental ℚ ((Real.pi * u.im : ℝ) : ℂ)) := by sorry
end DiazModulus
