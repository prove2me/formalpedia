-- Prove2me | Theorems.Thm_FiniteEnergyPlane_hasDerivAt_im_conj_mul_loopEigen
-- name    : FiniteEnergyPlane.hasDerivAt_im_conj_mul_loopEigen
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-01T21:03:14.533904+00:00
-- url     : https://prove2.me/theorems/3e377fde-28e8-46fa-a8fe-5d94c9c0b275
-- title:
--   Derivative of the cross term of two eigenfunctions of the asymptotic operator
-- statement:
--   Let $S_\infty:\mathbb{R}\to\mathbb{R}^{2\times2}$ be a continuous $1$-periodic loop of symmetric matrices and $A=-J_0\partial_t-S_\infty$ on $1$-periodic loops in $\mathbb{R}^2=\mathbb{C}$. Let $e_1,e_2$ be eigenfunctions of $A$ with eigenvalues $\mu_1,\mu_2$, viewed as loops $f_1,f_2$ in $\mathbb{C}$. Then for every $t$,
--   $$\frac{d}{dt}\operatorname{Im}\big(\overline{f_1(t)}\,f_2(t)\big)=(\mu_2-\mu_1)\operatorname{Re}\big(\overline{f_1(t)}\,f_2(t)\big).$$
--
--   An exact differential identity for pairs of eigenfunctions of the asymptotic operator, used to compare their winding numbers.
--
--   **Formalization Note** Eigenfunctions are `IsLoopEigen Sinf μ e` (`FiniteEnergyPlane_Asymptotics`: smooth, $1$-periodic, not identically zero, $-J_0e'-S_\infty e=\mu e$); symmetry and continuity are `CauchyRiemannIndex.IsSymLoop Sinf`; $f_j$ is `fun t => vecToC (e_j t)` and the conclusion is a `HasDerivAt` statement at every `t`.
-- source:
--   C. Wendl, Lectures on Symplectic Field Theory (2026 notes), arXiv:1612.01009, Section 3.7, proof of Theorem 3.7.1; H. Hofer, K. Wysocki, E. Zehnder, GAFA 5 (1995), Section 3.

import Definitions.Def_FiniteEnergyPlane_Winding

namespace FiniteEnergyPlane

/-- For eigenfunctions `e₁, e₂` of `A = -J₀ ∂ₜ - S∞` (symmetric `S∞`) with eigenvalues `μ₁, μ₂`,
read as loops `f₁, f₂` in `ℂ`, the imaginary part of `conj f₁ · f₂` has derivative
`(μ₂ - μ₁) Re(conj f₁ · f₂)`. -/
theorem hasDerivAt_im_conj_mul_loopEigen (Sinf : ℝ → CauchyRiemannIndex.Mat 1)
    (hSinf : CauchyRiemannIndex.IsSymLoop Sinf) {μ₁ μ₂ : ℝ}
    {e₁ e₂ : ℝ → CauchyRiemannIndex.Vec 1} (h₁ : IsLoopEigen Sinf μ₁ e₁)
    (h₂ : IsLoopEigen Sinf μ₂ e₂) (t : ℝ) :
    HasDerivAt (fun s => (starRingEnd ℂ (vecToC (e₁ s)) * vecToC (e₂ s)).im)
      ((μ₂ - μ₁) * (starRingEnd ℂ (vecToC (e₁ t)) * vecToC (e₂ t)).re) t := by
  sorry

end FiniteEnergyPlane
