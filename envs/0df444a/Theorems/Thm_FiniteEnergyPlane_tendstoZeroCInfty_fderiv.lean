-- Prove2me | Theorems.Thm_FiniteEnergyPlane_tendstoZeroCInfty_fderiv
-- name    : FiniteEnergyPlane.tendstoZeroCInfty_fderiv
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-30T11:03:26.357343+00:00
-- url     : https://prove2.me/theorems/6eeefd48-2295-4675-8494-16f5237aa9bd
-- title:
--   Convergence to zero in C^∞ on a cylindrical end passes to the derivative
-- statement:
--   Let $F$ be a real normed space and $f:\mathbb{R}\times\mathbb{R}\to F$. If $f(s,t)\to0$ in $C^\infty$ as $s\to+\infty$, uniformly in $t$, then the derivative $Df:\mathbb{R}^2\to L(\mathbb{R}^2,F)$ also tends to $0$ in $C^\infty$.
--
--   Together with the companion statement for pairs, this lets $C^\infty$ convergence on a cylindrical end be fed into smooth nonlinear expressions in a function and its first derivatives.
--
--   **Formalization Note** `TendstoZeroCInfty f` means: $f$ is $C^\infty$ on some half-plane $(s_0,\infty)\times\mathbb{R}$, and for every $m$ the $m$-th Fréchet derivative $D^mf(s,t)$ tends to $0$ uniformly in $t$ as $s\to+\infty$.
-- source:
--   U. Hryniewicz, J. Symplectic Geom. 12 (2014), arXiv:1105.2077, Theorem 2.10; H. Hofer, K. Wysocki, E. Zehnder, Properties of pseudoholomorphic curves in symplectisations I: asymptotics, Ann. Inst. H. Poincaré Anal. Non Linéaire 13 (1996)

import Definitions.Def_FiniteEnergyPlane_Asymptotics

namespace FiniteEnergyPlane

/-- If `f → 0` in `C^∞` on the end, then so does its derivative `Df`. -/
theorem tendstoZeroCInfty_fderiv {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : ℝ × ℝ → F} (hf : TendstoZeroCInfty f) : TendstoZeroCInfty (fderiv ℝ f) := by
  sorry

end FiniteEnergyPlane
