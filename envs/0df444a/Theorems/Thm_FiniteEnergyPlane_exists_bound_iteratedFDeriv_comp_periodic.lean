-- Prove2me | Theorems.Thm_FiniteEnergyPlane_exists_bound_iteratedFDeriv_comp_periodic
-- name    : FiniteEnergyPlane.exists_bound_iteratedFDeriv_comp_periodic
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-30T14:54:55.056171+00:00
-- url     : https://prove2.me/theorems/16c922c2-456c-42bd-94a0-f65dd3670bac
-- title:
--   Phase-uniform derivative bounds for periodic compositions
-- statement:
--   Let $E$ be a finite-dimensional real normed space, $F$ a real normed space, $T,r>0$, $a\in\mathbb{R}$, and let $\Phi:\mathbb{R}\times E\to F$ be smooth on $\mathbb{R}\times B(0,r)$ with $\Phi(\varphi+T,v)=\Phi(\varphi,v)$ for $\|v\|<r$. Then for every $m\in\mathbb{N}$ and $B\in\mathbb{R}$ there is $M$ with the following property. Let $b\in\mathbb{R}$, $\Omega\subseteq\mathbb{R}^2$ open, $p\in\Omega$, and $V:\mathbb{R}^2\to E$ smooth on $\Omega$ with $\|V\|\le r/2$ on $\Omega$ and $\|D^iV(p)\|\le B$ for all $i\le m$. Then
--   $$\big\|D^m\big[q\mapsto\Phi(a\,q_2+b,\,V(q))\big](p)\big\|\le M .$$
--
--   The point is that $M$ depends only on $\Phi,T,r,a,m,B$, not on the phase $b$, the set $\Omega$, the point $p$ or the map $V$. This gives uniform derivative bounds for maps of the form $\Phi(a t+b,V(s,t))$ when the phase $b$ is chosen separately on different pieces of the domain.
--
--   **Formalization Note** Derivatives are `iteratedFDeriv ℝ` on $\mathbb{R}\times\mathbb{R}$ at the point `p`, and $q_2$ is `q.2`.
-- source:
--   Used for H. Hofer, K. Wysocki, E. Zehnder, Properties of pseudoholomorphic curves in symplectisations I: asymptotics (1996), Theorem 1.3

import Theorems.Thm_FiniteEnergyPlane_exists_bound_iteratedFDeriv_of_periodic

namespace FiniteEnergyPlane

open Metric
open scoped ContDiff

/-- Let `Φ(φ, v)` be smooth on `ℝ × B(0, r)` and `T`-periodic in `φ`. For each order `m` and bound
`B` there is `M` such that, for every `b ∈ ℝ`, every open `Ω ⊆ ℝ²`, every `p ∈ Ω` and every map `V`
smooth on `Ω` with `‖V‖ ≤ r / 2` on `Ω` and derivatives of order `≤ m` at `p` bounded by `B`, the
`m`-th derivative of `q ↦ Φ(a q₂ + b, V q)` at `p` is bounded by `M`. -/
theorem exists_bound_iteratedFDeriv_comp_periodic {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (Φ : ℝ × E → F) (T r a : ℝ) (hT : 0 < T) (hr : 0 < r)
    (hΦ : ContDiffOn ℝ ∞ Φ (Set.univ ×ˢ ball (0 : E) r))
    (hper : ∀ (φ : ℝ) (v : E), ‖v‖ < r → Φ (φ + T, v) = Φ (φ, v)) (m : ℕ) (B : ℝ) :
    ∃ M : ℝ, ∀ (b : ℝ) (V : ℝ × ℝ → E) (Ω : Set (ℝ × ℝ)) (p : ℝ × ℝ), IsOpen Ω → p ∈ Ω →
      ContDiffOn ℝ ∞ V Ω → (∀ q ∈ Ω, ‖V q‖ ≤ r / 2) →
      (∀ i ≤ m, ‖iteratedFDeriv ℝ i V p‖ ≤ B) →
      ‖iteratedFDeriv ℝ m (fun q : ℝ × ℝ => Φ (a * q.2 + b, V q)) p‖ ≤ M := by
  sorry

end FiniteEnergyPlane
