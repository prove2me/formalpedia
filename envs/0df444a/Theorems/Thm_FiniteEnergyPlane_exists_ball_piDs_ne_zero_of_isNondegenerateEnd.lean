-- Prove2me | Theorems.Thm_FiniteEnergyPlane_exists_ball_piDs_ne_zero_of_isNondegenerateEnd
-- name    : FiniteEnergyPlane.exists_ball_piDs_ne_zero_of_isNondegenerateEnd
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-02T20:29:23.869617+00:00
-- url     : https://prove2.me/theorems/8a022eb7-a39e-441f-a718-c3bdac12e5d7
-- title:
--   $\pi\,\partial_s u$ has no zeros near a nondegenerate puncture
-- statement:
--   Let $S=H^{-1}(1)\subset\mathbb{R}^4$ be a strictly star-shaped level and $J$ a smooth $d\lambda_0$-compatible complex structure on $\xi$. Let $z_0\in\mathbb{C}$, $r>0$, and let $u$ be a finite-energy $\tilde J$-holomorphic curve on the punctured disc $B(z_0,r)\setminus\{z_0\}$. Suppose $z_0$ is a puncture of sign $\varepsilon\in\{\pm1\}$ which is nondegenerate in the sense of Hryniewicz, Definition 2.9, with asymptotic orbit $P$, and suppose that $\Pi=\pi\,\partial_s(\mathrm{pr}\circ u)$ (in the global frame of $\xi$) takes nonzero values at points arbitrarily close to $z_0$. Then for some $\rho>0$, $\Pi$ has no zero on $B(z_0,\rho)\setminus\{z_0\}$.
--
--   Thus the zeros of $\pi\,du$ cannot accumulate at a nondegenerate puncture, which is needed for $\mathrm{wind}_\pi$ (Hryniewicz (14)) to be a finite sum.
--
--   **Formalization Note** The puncture condition is `IsNondegenerateEnd H u (cylEndAt z₀) P ε` with `ε = 1 ∨ ε = -1`; the orbit $P$ may be degenerate. $\Pi$ is `piDs H u`.
-- source:
--   U. Hryniewicz, J. Symplectic Geom. 12 (2014), arXiv:1105.2077, Section 2.2.4, discussion of formula (14) (auxiliary lemma)

import Definitions.Def_FiniteEnergyPlane_Winding

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Near a nondegenerate puncture `z₀` (Hryniewicz, Definition 2.9, either sign) of a finite-energy
curve on `B(z₀, r) \ {z₀}`, if `π ∂ₛu` has nonzero values arbitrarily close to `z₀`, then it has no
zeros at all on some punctured disc around `z₀`. -/
theorem exists_ball_piDs_ne_zero_of_isNondegenerateEnd (H : V 1 → ℝ)
    (hH : IsStrictlyStarShapedLevel H) (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (z₀ : ℂ) (r : ℝ) (hr : 0 < r) (u : ℂ → V 1)
    (hu : IsFiniteEnergyCurve H J (ball z₀ r \ {z₀}) u) (P : ReebOrbit H) (ε : ℝ)
    (hε : ε = 1 ∨ ε = -1) (hnd : IsNondegenerateEnd H u (cylEndAt z₀) P ε)
    (hfreq : ∀ ρ > (0 : ℝ), ∃ z ∈ ball z₀ ρ \ {z₀}, piDs H u z ≠ 0) :
    ∃ ρ > (0 : ℝ), ∀ z ∈ ball z₀ ρ \ {z₀}, piDs H u z ≠ 0 := by
  sorry

end FiniteEnergyPlane
