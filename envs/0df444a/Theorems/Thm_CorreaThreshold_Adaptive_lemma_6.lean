-- Prove2me | Theorems.Thm_CorreaThreshold_Adaptive_lemma_6
-- name    : CorreaThreshold.Adaptive.lemma_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T12:37:55.048508+00:00
-- url     : https://prove2.me/theorems/2e46c0f9-23b0-4ca8-945b-ad3f8fedafae
-- title:
--   Lemma 6, p. 1464 — (ODE) y′ = y(ln y − 1) − (β − 1), y(0) = 1 has a unique solution; it is decreasing and strictly convex, and y‴ > 0
-- statement:
--   Let $\beta>1.25$ and $0<T\le1$. Say that $y$ solves (ODE) on $[0,T]$ if $y$ is continuous on $[0,T]$, $y(0)=1$, $0<y(t)\le1$ and
--   $$y'(t)=y(t)\big(\ln y(t)-1\big)-(\beta-1)$$
--   (as a right derivative) for every $t\in[0,T)$. If $y$ solves (ODE) on $[0,T]$, then
--   1. every solution of (ODE) on $[0,T]$ coincides with $y$ on $[0,T]$;
--   2. $y$ is strictly decreasing and strictly convex on $[0,T]$;
--   3. $y'''(t)>0$ for every $t\in(0,T)$ (where $0<y(t)<1$).
--
--   The solution of (ODE) is the continuous majorant of the recursion (9) used in Lemma 7.
--
--   **Formalization Note** The paper states Lemma 6 on $[0,1]$ under the standing assumptions of §4, "$\beta>1.25$ and $y\in[0,1]$", which are hypotheses here. Existence is not asserted: for $\beta>\beta^*$ the solution reaches $0$ before $t=1$. Positivity on $[0,T)$ keeps $\ln y$ meaningful (Lean's $\ln0=0$). The third derivative is Mathlib's `iteratedDeriv 3`.
-- source:
--   Correa, Foncea, Hoeksma, Oosterwijk, Vredeveld, Posted price mechanisms and optimal threshold strategies for random arrivals, Math. Oper. Res. 46 (2021), p. 1464, Lemma 6 (with (ODE) and §4's standing assumptions); proof pp. 1475–1476

import Mathlib
import Definitions.Def_CorreaThreshold_Adaptive_Setting

namespace CorreaThreshold.Adaptive

open MeasureTheory ProbabilityTheory

theorem lemma_6 (β : ℝ) (hβ : 5 / 4 < β) (T : ℝ) (hT : T ∈ Set.Ioc 0 1) (y : ℝ → ℝ)
    (hy : IsODESol β y T) :
    (∀ y' : ℝ → ℝ, IsODESol β y' T → Set.EqOn y y' (Set.Icc 0 T)) ∧
      StrictAntiOn y (Set.Icc 0 T) ∧
      StrictConvexOn ℝ (Set.Icc 0 T) y ∧
      ∀ t ∈ Set.Ioo 0 T, 0 < iteratedDeriv 3 y t := by sorry

end CorreaThreshold.Adaptive
