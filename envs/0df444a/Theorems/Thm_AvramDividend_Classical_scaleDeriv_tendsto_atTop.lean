-- Prove2me | Theorems.Thm_AvramDividend_Classical_scaleDeriv_tendsto_atTop
-- name    : AvramDividend.Classical.scaleDeriv_tendsto_atTop
-- status  : Open
-- author  : @WillR
-- created : 2026-09-29T00:49:38.298912+00:00
-- url     : https://prove2.me/theorems/4f3d0581-72ec-4eaa-a037-bef712a9eb89
-- title:
--   The scale-function derivative W' tends to +infinity as x tends to +infinity, for q > 0
-- statement:
--   Let $X$ be a spectrally negative Lévy process satisfying the standing
--   assumptions, let $q>0$ and let $W=W^{(q)}$ be its $q$-scale function. Then
--   $$W^{(q)\prime}(x)\longrightarrow +\infty\qquad\text{as }x\to+\infty.$$
--
--   This is the exponential-growth statement for the scale function. For $q>0$ the
--   largest root $\Phi(q)$ of $\psi(\theta)=q$ is strictly positive, since
--   $\psi(0)=0<q$ and $\psi$ is convex and unbounded above, and the standard
--   asymptotics read
--   $$\lim_{x\to+\infty}\frac{W^{(q)}(x)}{e^{\Phi(q)x}}=\frac{1}{\psi'(\Phi(q))}\in(0,\infty).$$
--   So $W$ grows like a positive multiple of $e^{\Phi(q)x}$, and $W$ is
--   $C^1$ on $(0,\infty)$ because $q>0$, whence $W^{(q)\prime}(x)$ grows like
--   $\Phi(q)e^{\Phi(q)x}/\psi'(\Phi(q))$ and diverges to $+\infty$.
--
--   **Why it matters.** Finiteness of $c^*$ in Lemma 2(i) reduces to the infimum of
--   $W^{(q)\prime}$ on $(0,\infty)$ being attained at some $a>0$, or else being
--   bounded below by the right limit $W^{(q)\prime}(0+)$ — the dichotomy of
--   `scaleDeriv_inf_attained`. Quasi-convexity of $W^{(q)\prime}$
--   (`scaleDeriv_quasiconvex`) makes every sublevel set an interval, and the
--   dichotomy additionally needs that these intervals cannot escape to $+\infty$ as
--   the level approaches the infimum. That is precisely what this divergence to
--   $+\infty$ supplies.
--
--   **Formalization Note.** The conclusion is stated in `Tendsto` form, the usual
--   Lean shape for a limit at infinity. Writing it as `Tendsto (deriv W) atTop
--   atTop` keeps the statement about the ordinary real derivative, so no part of
--   this fact needs the extended-real `derivZeroPlus`.
-- source:
--   Avram, Palmowski, Pistorius, arXiv:math/0702893v1, p. 15 (Lemma 2(i)); exponential asymptotics W(x)/e^{Phi(q)x} -> 1/psi'(Phi(q)) for q > 0 as in arXiv:2506.10538 section 2.1 eq. (2.1) and Kyprianou, Fluctuations of Levy processes with applications, Thm 8.1

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open MeasureTheory Filter Set
open scoped NNReal ENNReal

namespace AvramDividend.Classical

/-- For `q > 0` the derivative of the `q`-scale function is unbounded above and in
fact diverges to `+∞` as `x → +∞`.

This is the companion of `scaleDeriv_quasiconvex`. Together they give the
dichotomy of `scaleDeriv_inf_attained`: quasi-convexity makes the sublevel sets
of `W'` intervals, and divergence to `+∞` prevents those intervals from
escaping to `+∞`, so the infimum of `W'` on `(0, ∞)` is either attained at some
`a > 0` or is bounded below by the right limit `W'(0+)`.

The source is the exponential asymptotics of the scale function: for `q > 0`,
`W(x)/e^{Φ(q) x} → 1/ψ'(Φ(q))` with `Φ(q) > 0`. -/
theorem scaleDeriv_tendsto_atTop {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W) :
    Tendsto (deriv W) atTop atTop := by sorry

end AvramDividend.Classical
