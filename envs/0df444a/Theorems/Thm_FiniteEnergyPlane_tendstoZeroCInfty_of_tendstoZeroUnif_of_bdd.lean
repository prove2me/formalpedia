-- Prove2me | Theorems.Thm_FiniteEnergyPlane_tendstoZeroCInfty_of_tendstoZeroUnif_of_bdd
-- name    : FiniteEnergyPlane.tendstoZeroCInfty_of_tendstoZeroUnif_of_bdd
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-30T10:14:33.336208+00:00
-- url     : https://prove2.me/theorems/0b05644b-d420-403d-9b35-ef0c680e3457
-- title:
--   Uniform convergence with bounded derivatives gives C-infinity convergence on a cylindrical end
-- statement:
--   Let $F$ be a real normed space, $s_0\in\mathbb{R}$, and let $f:\mathbb{R}^2\to F$ be $C^\infty$ on $(s_0,\infty)\times\mathbb{R}$. Suppose that $f(s,t)\to0$ as $s\to+\infty$, uniformly in $t$, and that for every $m\ge0$ the $m$-th derivative $D^mf$ is bounded on some half-plane $\{s\ge s_1\}$ (with $s_1$ depending on $m$). Then every derivative tends to zero:
--   $$\sup_{t\in\mathbb{R}}\|D^mf(s,t)\|\to0\qquad (s\to+\infty)\quad\text{for all }m\ge0,$$
--   that is, $f\to0$ in $C^\infty$ on the end.
--
--   So, on a cylindrical end, uniform $C^0$ convergence to $0$ together with uniform bounds on all derivatives already gives $C^\infty$ convergence to $0$.
--
--   **Formalization Note** Uniform convergence is `TendstoZeroUnif f`, and $C^\infty$ convergence is `TendstoZeroCInfty f` (smooth on some $(s_0,\infty)\times\mathbb{R}$, every `iteratedFDeriv ℝ m f (s, t)` tends to $0$ uniformly in $t$). The bounds are on the full Fréchet derivatives `iteratedFDeriv ℝ m f`.
-- source:
--   Used for U. Hryniewicz, J. Symplectic Geom. 12 (2014), arXiv:1105.2077, Theorems 2.10-2.11, and H. Hofer, K. Wysocki, E. Zehnder, Properties of pseudoholomorphic curves in symplectisations I: asymptotics, Ann. Inst. H. Poincaré Anal. Non Linéaire 13 (1996)

import Definitions.Def_FiniteEnergyPlane_Asymptotics

namespace FiniteEnergyPlane

open scoped ContDiff

/-- If `f` is smooth on `(s₀, ∞) × ℝ`, tends to `0` uniformly in `t` as `s → +∞`, and each
derivative `D^m f` is bounded on some half-plane `s ≥ s₁`, then `f → 0` in `C^∞` on the end. -/
theorem tendstoZeroCInfty_of_tendstoZeroUnif_of_bdd {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (f : ℝ × ℝ → F) (s₀ : ℝ)
    (hf : ContDiffOn ℝ ∞ f (Set.Ioi s₀ ×ˢ Set.univ)) (h0 : TendstoZeroUnif f)
    (hB : ∀ m : ℕ, ∃ B s₁ : ℝ, ∀ s ≥ s₁, ∀ t : ℝ, ‖iteratedFDeriv ℝ m f (s, t)‖ ≤ B) :
    TendstoZeroCInfty f := by
  sorry

end FiniteEnergyPlane
