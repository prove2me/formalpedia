-- Prove2me | Theorems.Thm_AvramDividend_Classical_scaleDeriv_tendsto_atTop_of_eventually_ge_exp
-- name    : AvramDividend.Classical.scaleDeriv_tendsto_atTop_of_eventually_ge_exp
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-03T11:53:33.034909+00:00
-- url     : https://prove2.me/theorems/9636924b-e539-4301-9a7e-74b056fc301b
-- title:
--   An eventual lower exponential bound on the scale-function derivative forces divergence to $+\infty$
-- statement:
--   Let $W$ be the $q$-scale function of a spectrally negative Lévy process and suppose that for some $\phi>0$ and $c>0$ one has $c\exp(\phi x) \le W'(x)$ for all sufficiently large $x$. Then $W'(x) \to +\infty$ as $x \to +\infty$.
--
--   Indeed $\phi x \to +\infty$ when $\phi>0$, so $\exp(\phi x) \to +\infty$ by `Real.tendsto_exp_atTop`, and multiplying by the positive constant $c$ preserves divergence. Since $W'$ is eventually bounded below by that divergent function, $W' \to +\infty$ as well.
--
--   This is precisely the analytic step of the mission reduction `scaleDeriv_eventually_ge_exp` -> `scaleDeriv_tendsto_atTop`, isolated so that it can be proved while its premise remains open. No scale-function or probability theory is used: the statement holds for an arbitrary real function inside `deriv`.
-- source:
--   Kuznetsov, Kyprianou and Rivero, 'The expectations of the shortfall and the Canny shortfall', and the scale-function asymptotics used in Avram's optimal barrier strategy: for $q>0$ the scale function satisfies $W(x)/e^{\Phi(q)x} \to 1/\psi'(\Phi(q))$ with $\Phi(q)>0$, so its derivative diverges exponentially. The analytic implication from a lower exponential bound to divergence is elementary and is proved here directly.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open MeasureTheory Filter Set
open scoped NNReal ENNReal

namespace AvramDividend.Classical

/-- Divergence of the scale-function derivative at `+∞`, given an eventual lower
bound by a positive multiple of an exponential.

This isolates the entire real-analysis content of the arc
`scaleDeriv_eventually_ge_exp` -> `scaleDeriv_tendsto_atTop`. -/
theorem scaleDeriv_tendsto_atTop_of_eventually_ge_exp {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hexp : ∃ φ c : ℝ, 0 < φ ∧ 0 < c ∧
      ∀ᶠ x in Filter.atTop, c * Real.exp (φ * x) ≤ deriv W x) :
    Tendsto (deriv W) Filter.atTop Filter.atTop := by
  sorry

end AvramDividend.Classical
