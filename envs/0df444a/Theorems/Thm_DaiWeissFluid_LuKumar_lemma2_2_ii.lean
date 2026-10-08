-- Prove2me | Theorems.Thm_DaiWeissFluid_LuKumar_lemma2_2_ii
-- name    : DaiWeissFluid.LuKumar.lemma2_2_ii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T03:05:09.060908+00:00
-- url     : https://prove2.me/theorems/94f4fff6-af45-463c-8791-27fac5159123
-- title:
--   Lemma 2.2(ii) — extinction under negative drift
-- statement:
--   Let $g:[0,\infty)\to[0,\infty)$ be absolutely continuous on every bounded interval, and let $\varepsilon>0$. Assume that, almost everywhere at positive times where $g(t)>0$ and its derivative exists, $\dot g(t)\le-\varepsilon$. Then
--   $$g(t)=0\quad(t\ge g(0)/\varepsilon),\qquad g\text{ is nonincreasing on }[0,\infty).$$
--   In particular, once the function reaches zero it remains zero. This real-analysis criterion turns a Lyapunov drift bound into a uniform emptying time.
--
--   **Formalization Note** The printed lemma uses $\dot g< -\varepsilon$, but every application in this paper uses $\le-\varepsilon$; this statement uses the non-strict inequality. “Almost everywhere” is with respect to Lebesgue measure, and a regular point is represented by `HasDerivAt`.
-- source:
--   Dai and Weiss, Stability and instability of fluid models for reentrant lines, Math. Oper. Res. 21(1) (1996), p. 120, Lemma 2.2(ii), with the non-strict drift reading used in Theorems 3.1, 4.3, 4.4, 5.1 and 6.1

import Mathlib
import Definitions.Def_DaiWeissFluid_LuKumar_FluidModel
import Definitions.Def_DaiWeissFluid_LuKumar_Network

namespace DaiWeissFluid.LuKumar

/-- Lemma 2.2(ii), with the non-strict drift inequality used throughout the paper. -/
theorem lemma2_2_ii (g : ℝ → ℝ)
    (hac : ∀ a b, 0 ≤ a → a ≤ b → AbsolutelyContinuousOnInterval g a b)
    (hg : ∀ s, 0 ≤ s → 0 ≤ g s) (ε : ℝ) (hε : 0 < ε)
    (hdrift : ∀ᵐ t : ℝ ∂MeasureTheory.volume,
      0 < t → 0 < g t → ∀ d, HasDerivAt g d t → d ≤ -ε) :
    (∀ t, g 0 / ε ≤ t → g t = 0) ∧ AntitoneOn g (Set.Ici 0) := by sorry

end DaiWeissFluid.LuKumar
