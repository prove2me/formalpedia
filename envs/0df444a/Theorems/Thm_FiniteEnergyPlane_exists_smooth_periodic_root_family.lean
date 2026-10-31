-- Prove2me | Theorems.Thm_FiniteEnergyPlane_exists_smooth_periodic_root_family
-- name    : FiniteEnergyPlane.exists_smooth_periodic_root_family
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-30T09:33:40.842072+00:00
-- url     : https://prove2.me/theorems/2afa1f36-ee4e-4c61-b803-5799767778aa
-- title:
--   Smooth periodic family of roots of a scalar equation near a curve of simple zeros
-- statement:
--   Let $E$ be a finite-dimensional real normed space, $T>0$, and let $G:(\mathbb{R}\times E)\times\mathbb{R}\to\mathbb{R}$, $((\varphi,v),\sigma)\mapsto G((\varphi,v),\sigma)$, be $C^\infty$ and $T$-periodic in $\varphi$. Suppose that $G((\varphi,0),0)=0$ and $\partial_\sigma G((\varphi,0),0)\neq0$ for every $\varphi$. Then for every $\delta_0>0$ there are $0<\delta\le\delta_0$, $r>0$ and a function $g:\mathbb{R}\times E\to\mathbb{R}$ such that
--
--   - $g$ is $C^\infty$ on $\mathbb{R}\times B(0,r)$, $T$-periodic in $\varphi$, and $g(\varphi,0)=0$;
--   - for $\|v\|<r$, $\sigma=g(\varphi,v)$ is the unique solution of $G((\varphi,v),\sigma)=0$ with $|\sigma|<\delta$.
--
--   So a periodic curve of simple zeros $\sigma=0$ continues to a smooth, periodic family of zeros on a uniform neighbourhood, with a uniform window of uniqueness. This is used to define the position along a periodic orbit of nearby points.
--
--   **Formalization Note** The $\sigma$-derivative is `deriv (fun σ => G ((φ, 0), σ)) 0`; the periodicity of $g$ is stated for all $(\varphi,v)$.
-- source:
--   Used for U. Hryniewicz, J. Symplectic Geom. 12 (2014), arXiv:1105.2077, Theorems 2.10-2.11, and H. Hofer, K. Wysocki, E. Zehnder, Properties of pseudoholomorphic curves in symplectisations I: asymptotics, Ann. Inst. H. Poincaré Anal. Non Linéaire 13 (1996)

import Mathlib

namespace FiniteEnergyPlane

open Metric
open scoped ContDiff

/-- A smooth family of roots of a scalar equation near a periodic curve of simple zeros.
Let `G((φ, v), σ)` be smooth, `T`-periodic in `φ`, with `G((φ, 0), 0) = 0` and
`∂_σ G((φ, 0), 0) ≠ 0` for every `φ`. Then for every `δ₀ > 0` there are `0 < δ ≤ δ₀`, `r > 0` and
a function `g`, smooth on `ℝ × B(0, r)`, `T`-periodic in `φ`, with `g(φ, 0) = 0`, such that for
`‖v‖ < r` the number `g(φ, v)` is the unique root `σ` of `G((φ, v), σ) = 0` with `|σ| < δ`. -/
theorem exists_smooth_periodic_root_family {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (G : (ℝ × E) × ℝ → ℝ) (hG : ContDiff ℝ ∞ G) (T : ℝ) (hT : 0 < T)
    (hper : ∀ (φ : ℝ) (v : E) (σ : ℝ), G ((φ + T, v), σ) = G ((φ, v), σ))
    (h0 : ∀ φ : ℝ, G ((φ, 0), 0) = 0)
    (hd : ∀ φ : ℝ, deriv (fun σ : ℝ => G ((φ, 0), σ)) 0 ≠ 0)
    (δ₀ : ℝ) (hδ₀ : 0 < δ₀) :
    ∃ δ r : ℝ, 0 < δ ∧ δ ≤ δ₀ ∧ 0 < r ∧ ∃ g : ℝ × E → ℝ,
      ContDiffOn ℝ ∞ g (Set.univ ×ˢ ball (0 : E) r) ∧
      (∀ (φ : ℝ) (v : E), g (φ + T, v) = g (φ, v)) ∧ (∀ φ : ℝ, g (φ, 0) = 0) ∧
      ∀ (φ : ℝ) (v : E), ‖v‖ < r →
        |g (φ, v)| < δ ∧ G ((φ, v), g (φ, v)) = 0 ∧
        ∀ σ : ℝ, |σ| < δ → G ((φ, v), σ) = 0 → σ = g (φ, v) := by
  sorry

end FiniteEnergyPlane
