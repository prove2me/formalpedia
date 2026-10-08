-- Prove2me | Theorems.Thm_DaiWeissFluid_LBFS_lemma2_2_ii
-- name    : DaiWeissFluid.LBFS.lemma2_2_ii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T02:30:12.990292+00:00
-- url     : https://prove2.me/theorems/ed97e616-71be-496d-9f3b-92ea98adb7a8
-- title:
--   Lemma 2.2(ii) — negative drift gives finite extinction
-- statement:
--   Let $g$ be a function that is absolutely continuous on every interval $[a,b] \subseteq [0,\infty)$ and nonnegative on $[0,\infty)$, and let $\varepsilon > 0$. Assume that for almost every $t > 0$ (Lebesgue measure), if $g(t) > 0$ and $g$ is differentiable at $t$, then $\dot g(t) \le -\varepsilon$. Then, with $\delta = g(0)/\varepsilon$,
--   $$
--   g(t) = 0 \quad\text{for all } t \ge \delta ,
--   $$
--   and $g$ is nonincreasing on $[0,\infty)$; in particular, once $g$ reaches zero it stays there.
--
--   This is the extinction criterion used to turn a negative drift of a Lyapunov function or of a single buffer level into a finite emptying time; the proof of Theorem 4.3 applies it to the first nonempty buffer, and the proof of Theorem 4.4 to the total fluid content $|Q(t)|$.
--
--   **Formalization Note** The paper prints the hypothesis with a strict inequality $\dot g(t) < -\varepsilon$; every application in the paper uses $\dot g(t) \le -\varepsilon$, which is the weaker hypothesis stated here, so the statement is stronger than the printed one. Absolute continuity is `AbsolutelyContinuousOnInterval g a b` for all $0 \le a \le b$. "Almost everywhere at regular points" is `∀ᵐ t` with respect to Lebesgue measure, quantifying over every derivative value `d` with `HasDerivAt g d t`.
-- source:
--   Dai and Weiss, Stability and instability of fluid models for reentrant lines, Math. Oper. Res. 21(1) (1996), p. 120, Lemma 2.2(ii)

import Mathlib

namespace DaiWeissFluid.LBFS

/-- Lemma 2.2(ii): extinction and monotonicity under negative drift at positive values. -/
theorem lemma2_2_ii (g : ℝ → ℝ)
    (hac : ∀ a b, 0 ≤ a → a ≤ b → AbsolutelyContinuousOnInterval g a b)
    (hg : ∀ s, 0 ≤ s → 0 ≤ g s) (ε : ℝ) (hε : 0 < ε)
    (hdrift : ∀ᵐ t ∂MeasureTheory.volume, 0 < t → 0 < g t →
      ∀ d, HasDerivAt g d t → d ≤ -ε) :
    (∀ t, g 0 / ε ≤ t → g t = 0) ∧ AntitoneOn g (Set.Ici 0) := by sorry

end DaiWeissFluid.LBFS
