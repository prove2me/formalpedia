-- Prove2me | Theorems.Thm_FiniteEnergyPlane_tendstoZeroCInfty_comp_periodic_of_drift
-- name    : FiniteEnergyPlane.tendstoZeroCInfty_comp_periodic_of_drift
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-30T15:54:27.723024+00:00
-- url     : https://prove2.me/theorems/71ec1fc0-e47e-49db-ad3f-7acc8cdb5bf9
-- title:
--   Composition with a periodic map along a drifting phase tends to zero in C^∞
-- statement:
--   Let $E$ be a finite-dimensional real normed space, $F$ a real normed space, $T,r>0$, $a\in\mathbb{R}$, and let $\Phi:\mathbb{R}\times E\to F$ be smooth on $\mathbb{R}\times B(0,r)$ with $\Phi(\varphi+T,v)=\Phi(\varphi,v)$ for $\|v\|<r$ and $\Phi(\varphi,0)=0$ for all $\varphi$. Let $\theta:\mathbb{R}^2\to\mathbb{R}$ be smooth on a half-plane $(s_2,\infty)\times\mathbb{R}$ such that, for every $m\ge1$, the derivative $D^m\theta(s,t)$ is bounded for $s$ large, uniformly in $t$; no bound on $\theta$ itself is assumed. If $v:\mathbb{R}^2\to E$ tends to $0$ in $C^\infty$ as $s\to+\infty$ (smooth on a half-plane, every derivative tending to $0$ uniformly in $t$), then
--   $$(s,t)\mapsto\Phi\big(a t+\theta(s,t),\,v(s,t)\big)$$
--   also tends to $0$ in $C^\infty$ as $s\to+\infty$.
--
--   This extends `tendstoZeroCInfty_comp_periodic` (the case of a constant phase $\theta\equiv b$) to a phase that drifts slowly, as happens for tube coordinates around a periodic orbit when the asymptotic phase is not yet known to converge.
--
--   **Formalization Note** "Tends to $0$ in $C^\infty$" is `TendstoZeroCInfty`. Derivatives are `iteratedFDeriv ℝ` on $\mathbb{R}\times\mathbb{R}$, and $t$ is `p.2`.
-- source:
--   Used for H. Hofer, K. Wysocki, E. Zehnder, Properties of pseudoholomorphic curves in symplectisations I: asymptotics (1996), Theorem 1.3

import Definitions.Def_FiniteEnergyPlane_Asymptotics

namespace FiniteEnergyPlane

open Metric
open scoped ContDiff

/-- Let `Φ(φ, v)` be smooth on `ℝ × B(0, r)`, `T`-periodic in `φ`, with `Φ(φ, 0) = 0`. Let `θ` be
smooth on a half-plane `(s₂, ∞) × ℝ` with every derivative of order `≥ 1` bounded there for large
`s` (`θ` itself need not be bounded). If `v(s, t) → 0` in `C^∞` on the end, then so does
`Φ(a t + θ(s, t), v(s, t))`, for any `a ∈ ℝ`. -/
theorem tendstoZeroCInfty_comp_periodic_of_drift {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (Φ : ℝ × E → F) (T r a : ℝ) (hT : 0 < T) (hr : 0 < r)
    (hΦ : ContDiffOn ℝ ∞ Φ (Set.univ ×ˢ ball (0 : E) r))
    (hper : ∀ (φ : ℝ) (v : E), ‖v‖ < r → Φ (φ + T, v) = Φ (φ, v))
    (h0 : ∀ φ : ℝ, Φ (φ, 0) = 0) (θ : ℝ × ℝ → ℝ)
    (hθs : ∃ s₂ : ℝ, ContDiffOn ℝ ∞ θ (Set.Ioi s₂ ×ˢ Set.univ))
    (hθ : ∀ m : ℕ, 1 ≤ m → ∃ B s₂ : ℝ, ∀ s ≥ s₂, ∀ t : ℝ, ‖iteratedFDeriv ℝ m θ (s, t)‖ ≤ B)
    (v : ℝ × ℝ → E) (hv : TendstoZeroCInfty v) :
    TendstoZeroCInfty (fun p : ℝ × ℝ => Φ (a * p.2 + θ p, v p)) := by
  sorry

end FiniteEnergyPlane
