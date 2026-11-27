-- Prove2me | Theorems.Thm_FiniteEnergyPlane_isLittleO_sub_nhdsWithin_range_of_isPrime
-- name    : FiniteEnergyPlane.isLittleO_sub_nhdsWithin_range_of_isPrime
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-27T00:10:47.73971+00:00
-- url     : https://prove2.me/theorems/f82a7b14-bba4-54c7-a1ed-a95a049509b1
-- title:
--   Secant directions of a prime periodic Reeb orbit are asymptotically tangent
-- statement:
--   Let $S = H^{-1}(1) \subset \mathbb{R}^{2n+2}$ be a strictly star-shaped level, $P = (x, T)$ a prime periodic Reeb orbit on $S$ (so $T$ is its least positive period), and $q = x(\tau_0)$ a point on it. Let $L : \mathbb{R}^{2n+2} \to F$ be a continuous linear map into a real normed space with $L(R(q)) = 0$, where $R$ is the Reeb vector field. Then $L(p - q) = o(\|p - q\|)$ as $p \to q$ with $p \in x(\mathbb{R})$.
--
--   Role: near each of its points, the image of a prime periodic orbit is tangent to the Reeb direction, uniformly in the sense that every secant $p - q$ with $p$ on the orbit and close to $q$ is almost parallel to $R(q)$. This is used to show that a map whose values stay in the image of the orbit has its derivative in the Reeb line.
-- source:
--   H. Hofer, K. Wysocki, E. Zehnder, Properties of pseudoholomorphic curves in symplectisations II: Embedding controls and algebraic invariants, Geom. Funct. Anal. 5 (1995), proof of Theorem 4.4

import Definitions.Def_FiniteEnergyPlane_Winding

namespace FiniteEnergyPlane

open Metric Filter Topology Asymptotics

/-- Near a point `q = x(τ₀)` of a prime periodic Reeb orbit `P = (x, T)`, every continuous linear map
`L` killing the Reeb vector `R(q)` satisfies `L(p - q) = o(‖p - q‖)` as `p → q` inside `x(ℝ)`. -/
theorem isLittleO_sub_nhdsWithin_range_of_isPrime {n : ℕ} (H : V n → ℝ)
    (hH : IsStrictlyStarShapedLevel H) (P : ReebOrbit H) (hP : P.IsPrime) (τ₀ : ℝ)
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (L : V n →L[ℝ] F)
    (hL : L (reeb H (P.x τ₀)) = 0) :
    (fun p => L (p - P.x τ₀)) =o[𝓝[Set.range P.x] (P.x τ₀)] (fun p => p - P.x τ₀) := by
  sorry

end FiniteEnergyPlane
