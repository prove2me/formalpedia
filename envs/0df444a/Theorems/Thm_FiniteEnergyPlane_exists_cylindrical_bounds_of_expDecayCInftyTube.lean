-- Prove2me | Theorems.Thm_FiniteEnergyPlane_exists_cylindrical_bounds_of_expDecayCInftyTube
-- name    : FiniteEnergyPlane.exists_cylindrical_bounds_of_expDecayCInftyTube
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-14T18:38:27.220712+00:00
-- url     : https://prove2.me/theorems/bad9f1de-3660-4c8a-aa34-304437d859a5
-- title:
--   Cylindrical C^2 bounds for a map with an exponentially attained periodic model at infinity
-- statement:
--   Let $E$ be a real normed space, $0<\rho'<\rho$, $b>0$, and let $F:\mathbb C\times\mathbb C\to E$ be smooth on $\mathbb C\times B_\rho(0)$. Write $\zeta=e^{2\pi(s+it)}$. Suppose there are $\ell\in E$ and a map $M:\mathbb R\times\mathbb C\to E$, smooth on $\mathbb R\times B_\rho(0)$ and $1$-periodic in its first variable, such that
--   $$(s,t,w)\ \longmapsto\ F\big(e^{2\pi(s+it)},w\big)-s\,\ell-M(t,w)$$
--   decays like $e^{-bs}$ in $C^\infty$ as $s\to+\infty$, uniformly in $t\in\mathbb R$ and $w\in B_\rho(0)$. Then there is a constant $C$ such that for all $\zeta\in\mathbb C$, all $w$ with $|w|\le\rho'$ and all $(\Delta_1,\omega_1),(\Delta_2,\omega_2)\in\mathbb C\times\mathbb C$,
--   $$\|DF(\zeta,w)(\Delta_1,\omega_1)\|\le C\Big(\frac{|\Delta_1|}{1+|\zeta|}+|\omega_1|\Big),$$
--   $$\|D^2F(\zeta,w)(\Delta_1,\omega_1)(\Delta_2,\omega_2)\|\le C\Big(\frac{|\Delta_1|}{1+|\zeta|}+|\omega_1|\Big)\Big(\frac{|\Delta_2|}{1+|\zeta|}+|\omega_2|\Big).$$
--
--   In words: $F$ is uniformly $C^2$-bounded with respect to the cylindrical scale $|d\zeta|/(1+|\zeta|)$ on the base and the Euclidean scale on the fibre. Bounds of this form are what is needed to compare $F$ along perturbations of the base point that are small in cylindrical scale, for instance for the symplectization coordinates of a tubular parametrization around a finite-energy plane.
--
--   Formalization Note: `cylInf s t` is $e^{2\pi(s+it)}$, and `ExpDecayCInftyTube f ρ b` says that $f(s,t,w)$ is smooth for large $s$ and every iterated derivative is bounded by $C_m e^{-bs}$ for $s\ge s_m$, all $t$ and all $w\in B_\rho(0)$. $D^2F$ is `fderiv ℝ (fderiv ℝ F)`. The hypotheses are stated for arbitrary $\ell$ and $M$; no relation between $b$ and any other rate is assumed.
-- source:
--   Standard estimate in cylindrical coordinates; set-up of Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. AMS 364 (2012), Section 6

import Definitions.Def_FiniteEnergyPlane_Tube

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Cylindrical `C²` bounds of a map with an exponentially attained periodic model at `∞`. Let
`F : ℂ × ℂ → E` be smooth on `ℂ × ball 0 ρ` and suppose that in the coordinates
`ζ = e^{2π(s + it)}` the difference `F(ζ, w) - s • ℓ - M(t, w)`, with `M` smooth and `1`-periodic
in `t`, decays like `e^{-bs}` in `C^∞`, uniformly in `t` and `w ∈ ball 0 ρ`. Then for every
`ρ' < ρ` there is `C` such that on `ℂ × closedBall 0 ρ'`
`‖DF(ζ, w)(Δ, ω)‖ ≤ C (‖Δ‖/(1 + ‖ζ‖) + ‖ω‖)` and
`‖D²F(ζ, w)(Δ₁, ω₁)(Δ₂, ω₂)‖ ≤ C (‖Δ₁‖/(1 + ‖ζ‖) + ‖ω₁‖)(‖Δ₂‖/(1 + ‖ζ‖) + ‖ω₂‖)`. -/
theorem exists_cylindrical_bounds_of_expDecayCInftyTube {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (ρ b ρ' : ℝ) (hb : 0 < b) (hρ' : 0 < ρ') (hρ : ρ' < ρ)
    (F : ℂ × ℂ → E) (hF : ContDiffOn ℝ ∞ F (Set.univ ×ˢ ball (0 : ℂ) ρ)) (ℓ : E)
    (M : ℝ × ℂ → E) (hM : ContDiffOn ℝ ∞ M (Set.univ ×ˢ ball (0 : ℂ) ρ))
    (hMper : ∀ (t : ℝ) (w : ℂ), M (t + 1, w) = M (t, w))
    (hdec : ExpDecayCInftyTube (fun q : ℝ × ℝ × ℂ =>
      F (cylInf q.1 q.2.1, q.2.2) - q.1 • ℓ - M (q.2.1, q.2.2)) ρ b) :
    ∃ C : ℝ, ∀ ζ w : ℂ, w ∈ closedBall (0 : ℂ) ρ' →
      (∀ h : ℂ × ℂ, ‖fderiv ℝ F (ζ, w) h‖ ≤ C * (‖h.1‖ / (1 + ‖ζ‖) + ‖h.2‖)) ∧
      ∀ h k : ℂ × ℂ, ‖fderiv ℝ (fderiv ℝ F) (ζ, w) h k‖ ≤
        C * (‖h.1‖ / (1 + ‖ζ‖) + ‖h.2‖) * (‖k.1‖ / (1 + ‖ζ‖) + ‖k.2‖) := by
  sorry

end FiniteEnergyPlane
