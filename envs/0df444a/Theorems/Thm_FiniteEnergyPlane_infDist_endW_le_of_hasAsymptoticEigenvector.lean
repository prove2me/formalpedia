-- Prove2me | Theorems.Thm_FiniteEnergyPlane_infDist_endW_le_of_hasAsymptoticEigenvector
-- name    : FiniteEnergyPlane.infDist_endW_le_of_hasAsymptoticEigenvector
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-09T14:16:27.713422+00:00
-- url     : https://prove2.me/theorems/86d93fec-75bb-4cb1-a578-60946180f034
-- title:
--   Distance to the asymptotic orbit along an end with an asymptotic eigenvector
-- statement:
--   Let $S=H^{-1}(1)\subset\mathbb R^{2n+2}$ be strictly star-shaped, $P=(x,T)$ a periodic Reeb orbit on $S$, and let $u:\mathbb C\to\mathbb R^{2n+2}$ and a parametrization $e:\mathbb R\times\mathbb R\to\mathbb C$ of an end be such that $u$ has an asymptotic eigenvalue $\mu$ with an asymptotic eigenvector $v$ of $A_P$ along $e$ with sign $\varepsilon$, in the sense of Hryniewicz, Theorem 2.11. Write $w(s,t)=\mathrm{proj}(u(e(s,t)))\in S$. Then there are constants $C$ and $s_0$ such that
--   $$\operatorname{dist}\big(w(s,t),\,x(\mathbb R)\big)\le C\,e^{\varepsilon\mu s}\qquad\text{for all } s\ge s_0,\ t\in\mathbb R.$$
--
--   The statement turns the asymptotic representation of an end into an explicit rate at which the end approaches the image of its asymptotic orbit, for use in pointwise decay estimates of finite-energy curves.
--
--   Formalization Note: `HasAsymptoticEigenvector H J u e P ε μ v` is the representation of Theorem 2.11 (`v` an eigenvector of $A_P$ with eigenvalue $\mu$, $\varepsilon\mu<0$, and $w = \mathrm{proj}(x(\tau)+h)$ with $h=e^{\varepsilon\mu s}(v(\tau/T)+r)$, $r\to0$ in $C^\infty$). The distance is `Metric.infDist (endW H u e (s, t)) (Set.range P.x)`.
-- source:
--   Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. AMS 364 (2012), Theorem 2.11 and Section 6

import Definitions.Def_FiniteEnergyPlane_Asymptotics

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Distance to the orbit along an end with an asymptotic eigenvector. Let `u` have an asymptotic
eigenvalue `μ` and eigenvector `v` of `A_P` along the end `e`, with sign `ε` (Hryniewicz,
Theorem 2.11). Then for large `s` the distance from `w(s, t) = proj (u (e s t))` to the image of `P`
is at most `C e^{εμs}`, uniformly in `t`. -/
theorem infDist_endW_le_of_hasAsymptoticEigenvector {n : ℕ} (H : V n → ℝ)
    (hH : IsStrictlyStarShapedLevel H) (J : V n → V n →L[ℝ] V n) (u : ℂ → V n)
    (e : ℝ → ℝ → ℂ) (P : ReebOrbit H) (ε μ : ℝ) (v : ℝ → V n)
    (hv : HasAsymptoticEigenvector H J u e P ε μ v) :
    ∃ C s₀ : ℝ, ∀ s ≥ s₀, ∀ t : ℝ,
      infDist (endW H u e (s, t)) (Set.range P.x) ≤ C * Real.exp (ε * μ * s) := by
  sorry

end FiniteEnergyPlane
