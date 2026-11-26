-- Prove2me | Theorems.Thm_FiniteEnergyPlane_fderiv_eq_zero_of_dlambdaDensity_eq_zero
-- name    : FiniteEnergyPlane.fderiv_eq_zero_of_dlambdaDensity_eq_zero
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-26T17:38:32.010313+00:00
-- url     : https://prove2.me/theorems/f8f38f7e-48d6-5b0d-b84d-ce65406fc40e
-- title:
--   A pseudoholomorphic map is critical where its R-coordinate is critical and its d-lambda density vanishes
-- statement:
--   Let $S = H^{-1}(1) \subset \mathbb{R}^{2n+2}$ be strictly star-shaped, $J$ a compatible complex structure on $\xi$, and $\tilde J$ the induced almost complex structure on $\mathbb{R} \times S \cong \mathbb{R}^{2n+2} \setminus \{0\}$. Let $u : \mathbb{C} \to \mathbb{R}^{2n+2}$ be differentiable at $z$ with $u(z) \neq 0$ and $\bar\partial_{\tilde J} u(z) = 0$, and write $u = (a, w)$ with $a = \mathrm{aCoord} \circ u$, $w = \mathrm{proj} \circ u$. If $Da(z) = 0$ and $\omega_0(\partial_s w, \partial_t w)(z) = 0$, then $Du(z) = 0$.
--
--   Role: a pointwise rigidity statement: at a critical point of the $\mathbb{R}$-coordinate, a pseudoholomorphic map with vanishing $d\lambda$-density is critical; it is used to show that such maps with constant $\mathbb{R}$-coordinate and zero $d\lambda$-density are constant.
--
--   Formalization Note: the $d\lambda$-density is `dlambdaDensity H u z`.
-- source:
--   H. Hofer, Pseudoholomorphic curves in symplectizations with applications to the Weinstein conjecture in dimension three, Invent. Math. 114 (1993), 515-563, Section 2.2

import Definitions.Def_FiniteEnergyPlane_Setting

namespace FiniteEnergyPlane

/-- Let `u` be `J̃`-holomorphic at `z` (differentiable at `z`, `u z ≠ 0`, `∂̄_{J̃} u (z) = 0`), and
write `u = (a, w)`. If `z` is a critical point of `a = aCoord ∘ u` and the `dλ`-density
`ω₀(∂ₛw, ∂ₜw)` vanishes at `z`, then `Du(z) = 0`. -/
theorem fderiv_eq_zero_of_dlambdaDensity_eq_zero {n : ℕ} (H : V n → ℝ)
    (hH : IsStrictlyStarShapedLevel H) (J : V n → V n →L[ℝ] V n)
    (hJ : IsCompatibleXiStructure H J) (u : ℂ → V n) (z : ℂ)
    (hdu : DifferentiableAt ℝ u z) (hz : u z ≠ 0)
    (hhol : JHolomorphic.dbarJ (Jtilde H J) u z = 0)
    (ha : fderiv ℝ (fun z => aCoord H (u z)) z = 0) (hd : dlambdaDensity H u z = 0) :
    fderiv ℝ u z = 0 := by
  sorry

end FiniteEnergyPlane
