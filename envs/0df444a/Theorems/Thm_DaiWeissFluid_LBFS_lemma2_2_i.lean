-- Prove2me | Theorems.Thm_DaiWeissFluid_LBFS_lemma2_2_i
-- name    : DaiWeissFluid.LBFS.lemma2_2_i
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T02:30:14.83426+00:00
-- url     : https://prove2.me/theorems/3d841ad3-9eba-4df1-9baa-0abb342a72d5
-- title:
--   Lemma 2.2(i) — zero derivative at a zero of a nonnegative function
-- statement:
--   Let $g$ be a real function with $g(s) \ge 0$ for all $s \ge 0$, and let $t > 0$ be a time at which $g(t) = 0$ and the derivative $\dot g(t)$ exists. Then
--   $$
--   \dot g(t) = 0 .
--   $$
--
--   Applied to a buffer level $Q_k$, this says that an empty buffer has zero net drift at every regular time; it gives Proposition 4.2 (b).
--
--   **Formalization Note** The paper states the lemma for absolutely continuous nonnegative $g$; absolute continuity is not needed for part (i) and is dropped, which makes the statement stronger. The time is restricted to $t > 0$, since nonnegativity is only assumed on $[0,\infty)$ and a two-sided derivative at $t = 0$ would not be forced to vanish; every use in the paper is at a regular point $t > 0$. "The derivative exists" is `HasDerivAt g d t`.
-- source:
--   Dai and Weiss, Stability and instability of fluid models for reentrant lines, Math. Oper. Res. 21(1) (1996), p. 120, Lemma 2.2(i)

import Mathlib

namespace DaiWeissFluid.LBFS

/-- Lemma 2.2(i), at an interior regular point of a nonnegative path. -/
theorem lemma2_2_i (g : ℝ → ℝ) (hg : ∀ s, 0 ≤ s → 0 ≤ g s)
    (t : ℝ) (ht : 0 < t) (h0 : g t = 0) (d : ℝ)
    (hd : HasDerivAt g d t) : d = 0 := by sorry

end DaiWeissFluid.LBFS
