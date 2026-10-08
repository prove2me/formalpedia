-- Prove2me | Theorems.Thm_DaiWeissFluid_FBFS_lemma2_2_i
-- name    : DaiWeissFluid.FBFS.lemma2_2_i
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T02:28:59.000775+00:00
-- url     : https://prove2.me/theorems/0d77f76c-116d-49b3-ba2a-695032c2c9bd
-- title:
--   Lemma 2.2 (i) — a nonnegative function has zero derivative where it vanishes
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
--   Dai and Weiss, Stability and instability of fluid models for reentrant lines, Math. Oper. Res. 21(1) (1996), p. 120, Lemma 2.2 (i)

import Mathlib

namespace DaiWeissFluid.FBFS

/-- Lemma 2.2 (i), p. 120: if a function `g`, nonnegative on `[0, ∞)`, vanishes at a time `t > 0`
where it has derivative `d`, then `d = 0`. (The paper also assumes `g` absolutely continuous; the
claim does not need it.) -/
theorem lemma2_2_i (g : ℝ → ℝ) (hg : ∀ s, 0 ≤ s → 0 ≤ g s) (t : ℝ) (ht : 0 < t)
    (h0 : g t = 0) (d : ℝ) (hd : HasDerivAt g d t) : d = 0 := by sorry

end DaiWeissFluid.FBFS
