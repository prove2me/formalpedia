-- Prove2me | Theorems.Thm_DaiWeissFluid_ThreeBuffer_lemma2_2_ii
-- name    : DaiWeissFluid.ThreeBuffer.lemma2_2_ii
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T20:07:51.596066+00:00
-- url     : https://prove2.me/theorems/78713b71-2c99-4b44-b299-8af4b27cbf00
-- title:
--   Lemma 2.2 (ii) — a nonnegative absolutely continuous function with drift ≤ −ε while positive empties by g(0)/ε
-- statement:
--   Let $g : [0,\infty) \to \mathbb R$ be absolutely continuous on every compact interval $[a,b] \subseteq [0,\infty)$ and nonnegative. Suppose there is $\varepsilon > 0$ such that, for almost every $t > 0$ (Lebesgue), if $g(t) > 0$ and $g$ is differentiable at $t$ then $\dot g(t) \le -\varepsilon$. Then
--
--   $$
--   g(t) = 0 \quad \text{for all } t \ge \delta := \frac{g(0)}{\varepsilon},
--   $$
--
--   and $g$ is nonincreasing on $[0,\infty)$; in particular, once $g$ reaches zero it stays there.
--
--   This is the extinction lemma used in every stability proof of the paper: a Lyapunov function with a uniformly negative drift while positive reaches zero in a time bounded by its initial value.
--
--   **Formalization Note.** The paper prints the strict hypothesis $\dot g(t) < -\varepsilon$; every application in the paper uses $\dot g(t) \le -\varepsilon$, which is the weaker hypothesis and is the one stated here, so this statement implies the printed one. "Regular point" is encoded as `HasDerivAt g d t`; "almost everywhere" is with respect to Lebesgue measure on $\mathbb R$. Absolute continuity is Mathlib's `AbsolutelyContinuousOnInterval` on every $[a,b]$ with $0 \le a \le b$. Values of $g$ at negative times play no role in the hypotheses on $(0,\infty)$ beyond differentiability at points $t>0$.
-- source:
--   Dai and Weiss, Stability and instability of fluid models for reentrant lines, Math. Oper. Res. 21(1) (1996), p. 120, Lemma 2.2 (ii)

import Mathlib

namespace DaiWeissFluid.ThreeBuffer

open MeasureTheory in
/-- Lemma 2.2 (ii), p. 120: an absolutely continuous nonnegative `g` whose derivative is at most
`-ε` almost everywhere at regular points `t > 0` with `g t > 0` vanishes from `g(0)/ε` on, and is
nonincreasing on `[0, ∞)`. The paper prints the strict `ġ(t) < -ε`; every application uses `≤ -ε`,
which is the weaker hypothesis stated here. -/
theorem lemma2_2_ii (g : ℝ → ℝ)
    (hac : ∀ a b, 0 ≤ a → a ≤ b → AbsolutelyContinuousOnInterval g a b)
    (hg : ∀ s, 0 ≤ s → 0 ≤ g s) (ε : ℝ) (hε : 0 < ε)
    (hdrift : ∀ᵐ t ∂(volume : Measure ℝ),
      0 < t → 0 < g t → ∀ d, HasDerivAt g d t → d ≤ -ε) :
    (∀ t, g 0 / ε ≤ t → g t = 0) ∧ AntitoneOn g (Set.Ici 0) := by sorry

end DaiWeissFluid.ThreeBuffer
