-- Prove2me | Theorems.Thm_FiniteEnergyPlane_exists_tendsto_eq_of_tendsto_of_injective_fderiv
-- name    : FiniteEnergyPlane.exists_tendsto_eq_of_tendsto_of_injective_fderiv
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-21T10:38:45.728558+00:00
-- url     : https://prove2.me/theorems/9e2d57f8-35c4-4b9d-b28a-161497cf6890
-- title:
--   Convergent preimages under a C¹ map with injective derivative between equal-dimensional spaces
-- statement:
--   Let $E$ and $F$ be finite-dimensional real normed spaces of the same dimension, $U\subseteq E$ open, and $f:E\to F$ a map that is $C^1$ on $U$ with injective derivative $Df(p)$ at every $p\in U$. If $p\in U$ and $(y_k)$ is a sequence in $F$ with $y_k\to f(p)$, then there is a sequence $(x_k)$ in $E$ with $x_k\to p$ such that, for all sufficiently large $k$, $x_k\in U$ and $f(x_k)=y_k$.
--
--   Role: lets a sequence of points approaching the image of a $C^1$ embedding of equal dimension be written, eventually, as images of parameters converging to the base parameter. It is used to read off convergent parameters for maps that converge to a member of a smooth family of fast finite-energy planes.
--
--   **Formalization Note** Equal dimension is `Module.finrank ℝ E = Module.finrank ℝ F`; "$C^1$ on $U$" is `ContDiffOn ℝ 1 f U`. The sequence $(x_k)$ is defined for every $k$; only the eventual statements are asserted for it.
-- source:
--   Toward U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. Amer. Math. Soc. 364 (2012), 1859–1931, arXiv:0812.4076, Theorem 2.3(3)

import Mathlib

open Filter Topology

namespace FiniteEnergyPlane

/-- If `f : E → F` (equal finite dimensions) is `C¹` on an open set `U` with injective derivative
at every point of `U`, then every sequence converging to `f p`, `p ∈ U`, eventually has preimages
in `U` that converge to `p`. -/
theorem exists_tendsto_eq_of_tendsto_of_injective_fderiv {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (hdim : Module.finrank ℝ E = Module.finrank ℝ F) (f : E → F) (U : Set E) (hU : IsOpen U)
    (hf : ContDiffOn ℝ 1 f U) (hd : ∀ p ∈ U, Function.Injective (fderiv ℝ f p))
    (p : E) (hp : p ∈ U) (y : ℕ → F) (hy : Tendsto y atTop (𝓝 (f p))) :
    ∃ x : ℕ → E, Tendsto x atTop (𝓝 p) ∧ ∀ᶠ k in atTop, x k ∈ U ∧ f (x k) = y k := by
  sorry

end FiniteEnergyPlane
