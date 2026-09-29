-- Prove2me | Theorems.Thm_EisensteinSeries_hasSum_weierstrassZeta_sub_mul_G2
-- name    : EisensteinSeries.hasSum_weierstrassZeta_sub_mul_G2
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:40.316651+00:00
-- url     : https://prove2.me/theorems/64168bde-187a-5996-8d94-81ff1cdc577b
-- title:
--   Cotangent expansion of the Weierstrass zeta function
-- statement:
--   Let $\tau$ be a point of the upper half-plane, and let $z$ be a complex number which avoids the lattice $\mathbb{Z}\tau+\mathbb{Z}$, in the sense that $z \neq v_0\tau + v_1$ for every integer vector $v \colon \mathrm{Fin}\,2 \to \mathbb{Z}$. Write $Z(\tau,z) = \mathtt{weierstrassZeta}\,\tau\,z$ for the Weierstrass zeta value, defined as $1/z$ plus the unordered sum over all $v \colon \mathrm{Fin}\,2 \to \mathbb{Z}$ of the term $\frac{1}{z-(v_0\tau+v_1)} + \frac{1}{v_0\tau+v_1} + \frac{z}{(v_0\tau+v_1)^2}$, the term at $v = 0$ being set to $0$. Then the sequence indexed by $m \in \mathbb{N}$ whose $m$-th term is $$\pi\cot\bigl(\pi(z+(m+1)\tau)\bigr) + \pi\cot\bigl(\pi(z-(m+1)\tau)\bigr)$$ is summable, with sum $Z(\tau,z) - z\cdot(\mathtt{EisensteinSeries.G2}\ \tau) - \pi\cot(\pi z)$; here `EisensteinSeries.G2` is the project's weight-two Eisenstein series attached to $\tau$. Since the assertion is phrased as `HasSum` for a $\mathbb{C}$-valued family indexed by $\mathbb{N}$, it includes unconditional (hence absolute) convergence of the series over $m \geq 1$, and the classical identity $Z(\tau,z) = z\,G_2(\tau) + \pi\cot(\pi z) + \sum_{m \geq 1}\bigl(\pi\cot(\pi(z+m\tau)) + \pi\cot(\pi(z-m\tau))\bigr)$ after rearrangement.
--
--   This is the cotangent (Fourier-type) expansion of the Weierstrass zeta function of the lattice $\mathbb{Z}\tau+\mathbb{Z}$, the analytic identity from which the quasi-period relations of $Z(\tau,\cdot)$ and the $q$-expansion of weight-two Eisenstein series are read off. It is used in the derivation of the transformation behaviour of the zeta function under $z \mapsto z+1$, $z \mapsto z+\tau$ and scaling, and in the boundedness and summation statement for the weight-one Eisenstein series $\mathtt{eisensteinG1}$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_EisensteinSeries_hasSum_weierstrassZeta_sub_mul_G2.lean

import Mathlib
import Definitions.Def_EisensteinSeries_WeierstrassZeta

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Real

theorem EisensteinSeries.hasSum_weierstrassZeta_sub_mul_G2 (τ : UpperHalfPlane) (z : ℂ)
    (hz : ∀ v : Fin 2 → ℤ, z ≠ (v 0 : ℂ) * τ + v 1) :
    HasSum (fun m : ℕ => π * Complex.cot (π * (z + ((m : ℂ) + 1) * τ)) +
        π * Complex.cot (π * (z - ((m : ℂ) + 1) * τ)))
      (EisensteinSeries.weierstrassZeta τ z - z * EisensteinSeries.G2 τ -
        π * Complex.cot (π * z)) := by sorry
