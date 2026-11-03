-- Prove2me | Theorems.Thm_FiniteEnergyPlane_exists_ball_hasLoopWind_re_mul_add_im_mul
-- name    : FiniteEnergyPlane.exists_ball_hasLoopWind_re_mul_add_im_mul
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-02T20:47:02.109351+00:00
-- url     : https://prove2.me/theorems/a65a9b7f-1f0a-4fcc-bdc7-afe47f98668f
-- title:
--   Winding number of a twisted power $\mathrm{Re}(w^m)p+\mathrm{Im}(w^m)q$ near its zero
-- statement:
--   Let $z_0\in\mathbb{C}$, $R>0$, $m\in\mathbb{N}$, and let $p,q:\mathbb{C}\to\mathbb{C}$ be continuous on the disc $B(z_0,R)$ with
--   $$\operatorname{Im}\big(\overline{p(z_0)}\,q(z_0)\big)>0,$$
--   i.e. $w\mapsto \operatorname{Re}(w)\,p(z_0)+\operatorname{Im}(w)\,q(z_0)$ is an orientation-preserving real-linear isomorphism of $\mathbb{C}$. Suppose
--   $$F(z)=\operatorname{Re}\big((z-z_0)^m\big)\,p(z)+\operatorname{Im}\big((z-z_0)^m\big)\,q(z)\qquad (z\in B(z_0,R)).$$
--   Then there is $0<r\le R$ such that $F$ has no zero in $B(z_0,r)\setminus\{z_0\}$, and for every $0<\rho<r$ the loop $t\mapsto F(z_0+\rho e^{2\pi i t})$ has winding number $m$.
--
--   This computes the local index of a zero of a map that is, up to a continuously varying orientation-preserving real-linear change of coordinates, the power $(z-z_0)^m$.
--
--   **Formalization Note** $\operatorname{Im}(\overline{p}q)$ is `(starRingEnd ℂ (p z₀) * q z₀).im`; the circle is `z₀ + ccwLoop ρ t` and "winding number $m$" is `HasLoopWind` from `FiniteEnergyPlane_Winding`.
-- source:
--   U. Hryniewicz, J. Symplectic Geom. 12 (2014), arXiv:1105.2077, Section 2.2.4 (auxiliary lemma for the local index of zeros)

import Definitions.Def_FiniteEnergyPlane_Winding

namespace FiniteEnergyPlane

open Metric Filter Topology
open scoped Real

/-- Let `p, q` be continuous on `B(z₀, R)` with `Im(conj p(z₀) · q(z₀)) > 0` (so that
`w ↦ Re(w) p(z₀) + Im(w) q(z₀)` is an orientation-preserving real-linear isomorphism of `ℂ`), and let
`F(z) = Re((z - z₀)^m) p(z) + Im((z - z₀)^m) q(z)` on `B(z₀, R)`. Then on some smaller disc
`B(z₀, r)`, `F` has no zero other than `z₀`, and `F` has winding number `m` along every
counterclockwise circle `t ↦ z₀ + ρ e^{2πit}`, `0 < ρ < r`. -/
theorem exists_ball_hasLoopWind_re_mul_add_im_mul (F p q : ℂ → ℂ) (z₀ : ℂ) (R : ℝ) (hR : 0 < R)
    (m : ℕ) (hp : ContinuousOn p (ball z₀ R)) (hq : ContinuousOn q (ball z₀ R))
    (hpq : 0 < (starRingEnd ℂ (p z₀) * q z₀).im)
    (hF : ∀ z ∈ ball z₀ R,
      F z = (((z - z₀) ^ m).re : ℂ) * p z + (((z - z₀) ^ m).im : ℂ) * q z) :
    ∃ r > (0 : ℝ), r ≤ R ∧ (∀ z ∈ ball z₀ r, z ≠ z₀ → F z ≠ 0) ∧
      ∀ ρ ∈ Set.Ioo 0 r, HasLoopWind (fun t => F (z₀ + ccwLoop ρ t)) m := by
  sorry

end FiniteEnergyPlane
