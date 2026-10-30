-- Prove2me | Theorems.Thm_FiniteEnergyPlane_expDecayCInfty_of_tendstoZeroCInfty
-- name    : FiniteEnergyPlane.expDecayCInfty_of_tendstoZeroCInfty
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-29T20:20:24.493479+00:00
-- url     : https://prove2.me/theorems/bd7cff9b-223e-4e17-9dbb-48caf2ec5136
-- title:
--   Exponential $C^0$ decay and $C^\infty$ convergence give exponential $C^\infty$ decay on a half-cylinder
-- statement:
--   Let $F$ be a real normed space and $f:\mathbb{R}\times\mathbb{R}\to F$. Suppose $f$ tends to $0$ in $C^\infty$ as $s\to+\infty$: $f$ is $C^\infty$ on $(s_1,\infty)\times\mathbb{R}$ for some $s_1$, and for every $m$ the $m$-th derivative $D^mf(s,t)$ tends to $0$ uniformly in $t$. Suppose moreover that $\|f(s,t)\|\le Ce^{-\delta s}$ for all $s\ge s_0$ and all $t$. Then for every $b<\delta$ the function $f$ decays like $e^{-bs}$ in $C^\infty$: for every $m$ there are $C_m$ and $s_m$ with $\|D^mf(s,t)\|\le C_me^{-bs}$ for $s\ge s_m$ and all $t$.
--
--   This upgrades exponential $C^0$ decay to exponential $C^\infty$ decay at any slightly smaller rate, uniform over all derivative orders, for maps on a cylindrical end that are already known to converge in $C^\infty$.
--
--   **Formalization Note** The hypothesis is `TendstoZeroCInfty f` and the conclusion is `∀ b < δ, ExpDecayCInfty f b`, with derivatives `iteratedFDeriv ℝ m f`.
-- source:
--   Elementary real analysis; used for C. Wendl, Lectures on Symplectic Field Theory (2026 notes), Proposition 6.7.1, and U. Hryniewicz, J. Symplectic Geom. 12 (2014), Theorem 2.10

import Definitions.Def_FiniteEnergyPlane_Asymptotics

namespace FiniteEnergyPlane

open Filter Topology
open scoped ContDiff

/-- If `f(s, t)` tends to `0` in `C^∞` as `s → +∞` (uniformly in `t`) and `‖f(s, t)‖ ≤ C e^{-δs}`
for `s ≥ s₀`, then `f` decays in `C^∞` like `e^{-bs}` for every rate `b < δ`. -/
theorem expDecayCInfty_of_tendstoZeroCInfty {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : ℝ × ℝ → F) (hf : TendstoZeroCInfty f) (δ C s₀ : ℝ)
    (hdec : ∀ s ≥ s₀, ∀ t : ℝ, ‖f (s, t)‖ ≤ C * Real.exp (-(δ * s))) :
    ∀ b < δ, ExpDecayCInfty f b := by
  sorry

end FiniteEnergyPlane
