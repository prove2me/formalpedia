-- Prove2me | Theorems.Thm_AvramDividend_Classical_scaleDeriv_quasiconvex
-- name    : AvramDividend.Classical.scaleDeriv_quasiconvex
-- status  : Open
-- author  : @WillR
-- created : 2026-09-29T00:24:54.125733+00:00
-- url     : https://prove2.me/theorems/5e2e9baa-aabb-4c49-a40c-c829f0d1a06e
-- title:
--   The scale-function derivative W' is quasi-convex (single-valley) on (0, infinity)
-- statement:
--   Let $X$ be a spectrally negative Lévy process satisfying the standing
--   assumptions, let $q>0$ and let $W=W^{(q)}$ be its $q$-scale function. Then the
--   derivative $W^{(q)\prime}$ is **quasi-convex** on $(0,\infty)$: for every
--   $0<u<w<v$,
--   $$W^{(q)\prime}(w)\le \max\{W^{(q)\prime}(u),\,W^{(q)\prime}(v)\}.$$
--   Equivalently every sublevel set $\{x>0: W^{(q)\prime}(x)\le c\}$ is an interval.
--
--   This is the single-valley shape of $W'$. It follows from the standard
--   representation, valid for $x>0$ and $q>0$,
--   $$W^{(q)}(x)=\varphi'(q)e^{\varphi(q)x}-\hat f(x),$$
--   where $\varphi(q)=\Phi(q)>0$ is the largest root of $\psi(\theta)=q$ and
--   $\hat f$ is non-negative and completely monotone on $(0,\infty)$ (hence
--   nonincreasing, with $\hat f'\le 0$ nondecreasing). Thus
--   $W^{(q)\prime}(x)=\varphi'(q)\varphi(q)e^{\varphi(q)x}-\hat f'(x)$ is the
--   difference of a strictly increasing function and a nondecreasing function, and
--   in particular $W^{(q)\prime}$ cannot fall, rise, and then fall again.
--
--   **Why it matters.** Finiteness of $c^*$ in Lemma 2(i) reduces to the infimum of
--   $W^{(q)\prime}$ on $(0,\infty)$ being attained at some $a>0$, or else being
--   bounded below by the right limit $W^{(q)\prime}(0+)$. Quasi-convexity is exactly
--   the hypothesis that forces this dichotomy: a quasi-convex function has interval
--   sublevel sets, so its infimum is either attained, or approached only at an
--   endpoint. The unboundedness of $W^{(q)\prime}$ at $+\infty$ (from
--   $W^{(q)}(x)\sim e^{\Phi(q)x}/\psi'(\Phi(q))$) rules out the remaining
--   possibility that the infimum is approached only at $+\infty$ without being
--   attained, leaving $W^{(q)\prime}(0+)$ as the sole lower bound.
--
--   **Formalization Note.** The statement is the three-point quasi-convexity inequality
--   for `deriv W` on the open positive half-line, which is equivalent to the
--   interval property of the sublevel sets. The `Standing` hypothesis and the scale
--   function hypothesis are carried unchanged from `cstar_lt_top` and
--   `scaleDeriv_inf_attained` so that this child is directly reusable there.
-- source:
--   Avram, Palmowski, Pistorius, arXiv:math/0702893v1, p. 15 (Lemma 2(i)) and the scale-function representation of Kyprianou, Fluctuations of Levy processes with applications, Thm 8.1; see also arXiv:2506.10538 section 2.1 eq. (2.1) for the exponential growth W(x)/e^{Phi(q)x} -> 1/psi'(Phi(q)) when q > 0

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open MeasureTheory Set
open scoped NNReal ENNReal

namespace AvramDividend.Classical

/-- The derivative of the `q`-scale function is quasi-convex on `(0, inf)`: the
sublevel sets `{x > 0 | deriv W x <= c}` are intervals. Equivalently `W'` has the
single-valley shape forced by the decomposition
`W(x) = phi'(q) e^{phi(q) x} - fhat(x)` with `fhat` non-negative and completely
monotone, so `W' = (increasing) - (increasing)`.

This is the structural fact that makes the infimum of `W'` on `(0, inf)` either
attained or approached only at an endpoint of the interval, which is exactly what
`scaleDeriv_inf_attained` needs and what Lemma 2(i) rests on. -/
theorem scaleDeriv_quasiconvex {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W) :
    ∀ u v w : ℝ, 0 < u → u < w → w < v → deriv W w ≤ max (deriv W u) (deriv W v) := by sorry

end AvramDividend.Classical
