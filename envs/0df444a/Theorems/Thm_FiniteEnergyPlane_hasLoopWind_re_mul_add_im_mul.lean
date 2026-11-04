-- Prove2me | Theorems.Thm_FiniteEnergyPlane_hasLoopWind_re_mul_add_im_mul
-- name    : FiniteEnergyPlane.hasLoopWind_re_mul_add_im_mul
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-03T11:10:23.349413+00:00
-- url     : https://prove2.me/theorems/eb71e4d0-556a-4e2d-97ec-21bfa51842bb
-- title:
--   Winding number of $\mathrm{Re}(c)\,p+\mathrm{Im}(c)\,q$ for an orientation-preserving frame $(p,q)$
-- statement:
--   Let $c,p,q:\mathbb{R}\to\mathbb{C}$ be continuous $1$-periodic loops such that $\mathrm{Im}\big(\overline{p(t)}\,q(t)\big)>0$ for every $t$, i.e. for each $t$ the real-linear map $x+iy\mapsto x\,p(t)+y\,q(t)$ is an orientation-preserving isomorphism of $\mathbb{C}$. If $c$ has winding number $k$ and $p$ has winding number $m$, then the loop
--   $$t\mapsto \mathrm{Re}(c(t))\,p(t)+\mathrm{Im}(c(t))\,q(t)$$
--   has winding number $k+m$.
--
--   This computes the winding of a vector field written in a moving, possibly non-orthonormal, positively oriented frame: for instance $\pi\partial_s$ of a pseudoholomorphic curve composed with a reparametrisation of the domain, read in a global trivialisation of $\xi$.
--
--   **Formalization Note** Loops are `ℝ → ℂ`; "winding number $k$" is `HasLoopWind f k`. The hypotheses on $c$ and $p$ include continuity, periodicity and non-vanishing; for $q$ only continuity and periodicity are assumed.
-- source:
--   Used in U. Hryniewicz, J. Symplectic Geom. 12 (2014), arXiv:1105.2077, Lemma 2.15 (windings of $\pi\partial_s u$ in cylindrical coordinates)

import Definitions.Def_FiniteEnergyPlane_Winding

namespace FiniteEnergyPlane

/-- Let `c, p, q` be continuous `1`-periodic loops in `ℂ` with `Im(conj (p t) · q t) > 0` for all
`t` (so `x + iy ↦ x p(t) + y q(t)` is an orientation-preserving real-linear isomorphism of `ℂ`).
If `c` has winding number `k` and `p` has winding number `m`, then
`t ↦ Re(c t) p(t) + Im(c t) q(t)` has winding number `k + m`. -/
theorem hasLoopWind_re_mul_add_im_mul {c p q : ℝ → ℂ} {k m : ℤ} (hc : HasLoopWind c k)
    (hp : HasLoopWind p m) (hq : Continuous q) (hqp : Function.Periodic q 1)
    (hpq : ∀ t, 0 < (starRingEnd ℂ (p t) * q t).im) :
    HasLoopWind (fun t => ((c t).re : ℂ) * p t + ((c t).im : ℂ) * q t) (k + m) := by
  sorry

end FiniteEnergyPlane
