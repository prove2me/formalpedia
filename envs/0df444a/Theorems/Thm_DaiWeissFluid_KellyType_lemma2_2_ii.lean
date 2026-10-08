-- Prove2me | Theorems.Thm_DaiWeissFluid_KellyType_lemma2_2_ii
-- name    : DaiWeissFluid.KellyType.lemma2_2_ii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T02:31:31.410009+00:00
-- url     : https://prove2.me/theorems/d3b5fa83-9b04-4745-8a88-02a646fb7a9e
-- title:
--   Lemma 2.2 (ii) — a nonnegative function drifting down at rate ≥ ε while positive vanishes by g(0)/ε
-- statement:
--   Let $g : [0,\infty) \to \mathbb{R}$ be absolutely continuous on every compact interval and nonnegative, and let $\dot g$ denote its derivative where it exists. Suppose there is $\varepsilon > 0$ such that for almost every $t > 0$: if $g(t) > 0$ and $g$ is differentiable at $t$, then $\dot g(t) \le -\varepsilon$. Then
--
--   $$ g(t) = 0 \quad \text{for all } t \ge \delta := g(0)/\varepsilon, $$
--
--   and $g$ is nonincreasing on $[0,\infty)$, so once it reaches zero it stays there.
--
--   This is the extinction criterion that turns a Lyapunov drift bound into stability of a fluid model.
--
--   **Formalization Note** The paper prints the strict hypothesis $\dot g(t) < -\varepsilon$; every application in the paper (Theorems 3.1, 4.3, 4.4, 5.1, 6.1 and Lemma 3.2) supplies $\dot g(t) \le -\varepsilon$, so the lemma is stated with $\le$, a weaker hypothesis and hence a stronger lemma. "Regular point" is rendered as `HasDerivAt g d t`, "almost everywhere" as Lebesgue-a.e. Absolute continuity is required on every interval $[a,b] \subseteq [0,\infty)$.
-- source:
--   Dai and Weiss, Stability and instability of fluid models for reentrant lines, Math. Oper. Res. 21(1) (1996), p. 120, Lemma 2.2 (ii)

import Mathlib

namespace DaiWeissFluid.KellyType

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

end DaiWeissFluid.KellyType
