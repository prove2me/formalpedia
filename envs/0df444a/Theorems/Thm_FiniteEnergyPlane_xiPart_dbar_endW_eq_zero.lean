-- Prove2me | Theorems.Thm_FiniteEnergyPlane_xiPart_dbar_endW_eq_zero
-- name    : FiniteEnergyPlane.xiPart_dbar_endW_eq_zero
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-30T11:03:26.122728+00:00
-- url     : https://prove2.me/theorems/7cccf247-2fc3-4701-a7ce-4bfd9325c53d
-- title:
--   The contact-plane component of a finite-energy end satisfies the Cauchy–Riemann equation
-- statement:
--   Let $S=H^{-1}(1)\subset\mathbb{R}^{2n+2}$ be a strictly star-shaped level with contact planes $\xi$, $J$ a smooth $d\lambda_0$-compatible complex structure on $\xi$, and $u$ a finite-energy $\tilde J$-holomorphic curve on $D\setminus\{0\}$. In the cylindrical coordinates $e^{-2\pi(s+it)}$ at $0$ let $w(s,t)\in S$ be the radial projection of $u$. For $w\in S$ let $$\pi_w v=v-\frac{dH(w)v}{dH(w)w}\,w-\lambda_0(w)(v)\,R(w)$$ be the projection onto $\xi_w$ along $w$ and the Reeb vector $R(w)$. Then for all $s>0$ and $t$, $$\pi_w\partial_sw+J(w)\,\pi_w\partial_tw=0.$$
--
--   This is the $\xi$-part of the Cauchy–Riemann equation of $u$, written on the end and independent of the $\mathbb{R}$-coordinate.
--
--   **Formalization Note** `V n` is $\mathbb{R}^{2n+2}$, `IsStrictlyStarShapedLevel H` says $H$ is smooth and $S=H^{-1}(1)$ is strictly star-shaped with $dH(x)x>0$ on $S$, `reeb H` is the Reeb field $R=X_H/\lambda_0(X_H)$, `liouville x v` is $\lambda_0(x)v=\tfrac12\omega_0(x,v)$, `IsInXi H x v` means $v\in\xi_x=\ker\lambda_0(x)\cap\ker dH(x)$, and a `ReebOrbit H` is $P=(x,T)$ with $x'=R(x)$, $x(\mathbb{R})\subset S$, $x(\tau+T)=x(\tau)$, $T>0$. `endW H u cylEnd` is $w$, `IsFiniteEnergyCurve` bundles smoothness, $u\neq0$, $\tilde J$-holomorphicity (`Jtilde H J`) and finite Hofer energy, and `IsCompatibleXiStructure H J` is the compatibility of $J$ with $d\lambda_0$ on $\xi$.
-- source:
--   U. Hryniewicz, J. Symplectic Geom. 12 (2014), arXiv:1105.2077, Theorem 2.10; H. Hofer, K. Wysocki, E. Zehnder, Properties of pseudoholomorphic curves in symplectisations I: asymptotics, Ann. Inst. H. Poincaré Anal. Non Linéaire 13 (1996)

import Definitions.Def_FiniteEnergyPlane_Asymptotics

namespace FiniteEnergyPlane

open Metric

/-- Let `u` be a finite-energy `J̃`-holomorphic curve on `D \ {0}` and `w = proj ∘ u` in the
cylindrical coordinates `cylEnd` at `0`. With `π_w v = v - (dH(w) v / dH(w) w) w - λ₀(w)(v) R(w)`,
the projection onto `ξ_w` along `w` and the Reeb vector, `π_w ∂ₛw + J(w) π_w ∂ₜw = 0` for `s > 0`. -/
theorem xiPart_dbar_endW_eq_zero {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V n → V n →L[ℝ] V n) (hJ : IsCompatibleXiStructure H J) (u : ℂ → V n)
    (hu : IsFiniteEnergyCurve H J (ball 0 1 \ {0}) u) {s : ℝ} (hs : 0 < s) (t : ℝ) :
    let w := endW H u cylEnd (s, t)
    let πw : V n → V n := fun v =>
      v - (fderiv ℝ H w v / fderiv ℝ H w w) • w - liouville w v • reeb H w
    πw (fderiv ℝ (endW H u cylEnd) (s, t) (1, 0)) +
      J w (πw (fderiv ℝ (endW H u cylEnd) (s, t) (0, 1))) = 0 := by
  sorry

end FiniteEnergyPlane
