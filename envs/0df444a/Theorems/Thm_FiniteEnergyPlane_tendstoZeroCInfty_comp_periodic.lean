-- Prove2me | Theorems.Thm_FiniteEnergyPlane_tendstoZeroCInfty_comp_periodic
-- name    : FiniteEnergyPlane.tendstoZeroCInfty_comp_periodic
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-30T09:33:41.13173+00:00
-- url     : https://prove2.me/theorems/d0f3d95a-0888-465b-9121-07f416391bd9
-- title:
--   C-infinity convergence of a periodic map evaluated along a convergent family
-- statement:
--   Let $E$ be a finite-dimensional real normed space, $F$ a real normed space, $T,r>0$, $a,b\in\mathbb{R}$, and let $\Phi:\mathbb{R}\times E\to F$ be $C^\infty$ on $\mathbb{R}\times B(0,r)$, $T$-periodic in its first variable there, with $\Phi(\varphi,0)=0$. If $v:\mathbb{R}^2\to E$ satisfies $v(s,t)\to0$ in $C^\infty$, uniformly in $t$, as $s\to+\infty$, then also $$\Phi\big(at+b,\,v(s,t)\big)\to0\quad\text{in }C^\infty,\text{ uniformly in }t.$$
--
--   This carries $C^\infty$ convergence through coordinates built along a periodic orbit, such as tube coordinates near a Reeb orbit.
--
--   **Formalization Note** $C^\infty$ convergence is `TendstoZeroCInfty` (smooth on some $(s_0,\infty)\times\mathbb{R}$, every derivative tends to $0$ uniformly in $t$). $E$ is a finite-dimensional real normed space and $F$ any real normed space; $\Phi$ is only assumed smooth and periodic on $\mathbb{R}\times B(0,r)$.
-- source:
--   Used for U. Hryniewicz, J. Symplectic Geom. 12 (2014), arXiv:1105.2077, Theorems 2.10-2.11, and H. Hofer, K. Wysocki, E. Zehnder, Properties of pseudoholomorphic curves in symplectisations I: asymptotics, Ann. Inst. H. Poincaré Anal. Non Linéaire 13 (1996)

import Definitions.Def_FiniteEnergyPlane_Asymptotics

namespace FiniteEnergyPlane

open Metric
open scoped ContDiff

/-- Let `Φ(φ, v)` be smooth on `ℝ × B(0, r)`, `T`-periodic in `φ`, with `Φ(φ, 0) = 0`. If
`v(s, t) → 0` in `C^∞` on the end, then so does `Φ(a t + b, v(s, t))`, for any `a, b ∈ ℝ`. -/
theorem tendstoZeroCInfty_comp_periodic {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (Φ : ℝ × E → F) (T r a b : ℝ) (hT : 0 < T) (hr : 0 < r)
    (hΦ : ContDiffOn ℝ ∞ Φ (Set.univ ×ˢ ball (0 : E) r))
    (hper : ∀ (φ : ℝ) (v : E), ‖v‖ < r → Φ (φ + T, v) = Φ (φ, v))
    (h0 : ∀ φ : ℝ, Φ (φ, 0) = 0)
    (v : ℝ × ℝ → E) (hv : TendstoZeroCInfty v) :
    TendstoZeroCInfty (fun p : ℝ × ℝ => Φ (a * p.2 + b, v p)) := by
  sorry

end FiniteEnergyPlane
