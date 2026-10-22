-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_radial_filling_locally_convex_of_positive_tangential_hessian
-- name    : BirkhoffGlobalSection.radial_filling_locally_convex_of_positive_tangential_hessian
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-09-29T18:28:05.078169+00:00
-- url     : https://prove2.me/theorems/f36eb2ca-5ecb-439f-8110-a5a76e64de44
-- title:
--   Local convexity of a radial level-set filling from its tangential Hessian
-- statement:
--   Let $F:\mathbb R^4\to\mathbb R$ and let $S\subset\mathbb R^4$ be a compact regular zero level of $F$. Assume that $S$ is a radial graph over the unit three-sphere, with exactly one positive point on every ray, and that $F$ is strictly negative between the origin and the boundary. Assume also that the Hessian of $F$ is positive on every nonzero tangent vector to $S$. Define the radial filling
--
--   $$
--   K=\{t s:s\in S,\ 0\le t\le1\}.
--   $$
--
--   Then $K$ is closed and connected, and every point $x\in K$ has a neighborhood $U$ for which $K\cap U$ is convex.
--
--   This is the local differential-geometric half of Hadamard's ovaloid theorem, with the radial hypotheses fixing the enclosed side and supplying the global topology needed by Tietze--Nakajima.
--
--   **Formalization Note** Tangency is expressed as annihilation by $DF(s)$ through `HasPositiveTangentialHessianOn`.
-- source:
--   J. Hadamard, Sur certaines propriétés des trajectoires en dynamique, J. Math. Pures Appl. (5) 3 (1897), 331--387 (ovaloid theorem); H. Tietze, Math. Z. 28 (1928), 697--707; used for Joung--van Koert, https://arxiv.org/abs/2407.19159v3, Theorem 1.5 and Proposition 4.4.

import Definitions.Def_BirkhoffGlobalSection
import Mathlib.Analysis.Convex.Basic

namespace BirkhoffGlobalSection

open scoped Topology

/-- The differential-geometric step in Hadamard's ovaloid theorem, specialized to a
compact radial zero level: positive tangential Hessian and the inward sign convention
make the radial filling closed, connected, and locally convex. -/
theorem radial_filling_locally_convex_of_positive_tangential_hessian
    (F : Phase → ℝ) (S : Set Phase)
    (hS : IsCompact S)
    (hF0 : ∀ s ∈ S, F s = 0)
    (hreg : ∀ s ∈ S, fderiv ℝ F s ≠ 0)
    (hTH : HasPositiveTangentialHessianOn F S)
    (hray : ∀ x ∈ unitThreeSphere, ∃ r : ℝ, 0 < r ∧ (fun i : Fin 4 => r * x i) ∈ S)
    (huniq : ∀ x ∈ unitThreeSphere, ∀ r t : ℝ, 0 < r → 0 < t →
      (fun i : Fin 4 => r * x i) ∈ S → (fun i : Fin 4 => t * x i) ∈ S → r = t)
    (hneg : ∀ x ∈ unitThreeSphere, ∀ R : ℝ, 0 < R → (fun i : Fin 4 => R * x i) ∈ S →
      ∀ r : ℝ, 0 ≤ r → r < R → F (fun i : Fin 4 => r * x i) < 0) :
    let K : Set Phase :=
      {y : Phase | ∃ s ∈ S, ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ y = t • s}
    IsClosed K ∧ IsPreconnected K ∧
      ∀ x ∈ K, ∃ U : Set Phase, U ∈ 𝓝 x ∧ Convex ℝ (K ∩ U) := by sorry

end BirkhoffGlobalSection
