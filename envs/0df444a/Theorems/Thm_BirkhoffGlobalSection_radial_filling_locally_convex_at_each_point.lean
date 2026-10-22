-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_radial_filling_locally_convex_at_each_point
-- name    : BirkhoffGlobalSection.radial_filling_locally_convex_at_each_point
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-09-29T19:22:34.930302+00:00
-- url     : https://prove2.me/theorems/ef9d9521-b596-431d-97d9-9921e1f50c22
-- title:
--   Local convexity of a radial filling from positive tangential Hessian
-- statement:
--   Let $S$ be a compact radial subset of the regular zero set of a function $F:\mathbb R^4\to\mathbb R$ that is twice differentiable at every point of $S$. Suppose $S$ has exactly one positive point on each ray from the origin, the values of $F$ are negative inside those boundary points, and the Hessian of $F$ is positive on every nonzero tangent vector to $S$. For the radial filling
--
--   $$
--   K=\{ts:s\in S,\ 0\le t\le1\},
--   $$
--
--   every $x\in K$ has a neighborhood $U$ such that $K\cap U$ is convex.
--
--   This is the local curvature assertion needed before applying the Tietze–Nakajima theorem to deduce global convexity of the filling.
--
--   **Formalization Note** Tangent vectors are annihilated by the derivative of $F$; the positive Hessian condition is `HasPositiveTangentialHessianOn`.
-- source:
--   Joung--van Koert, Computational symplectic topology and symmetric orbits in the restricted three-body problem, https://arxiv.org/pdf/2407.19159v3, p. 20, proof of Theorem 1.5 citing Frauenfelder--van Koert (2018), Lemma 12.1.2; Tietze--Nakajima local convexity framework in Bjorndahl--Karshon, https://www.cambridge.org/core/services/aop-cambridge-core/content/view/B930E94943C7C26370B602AFE3C2A2C5/S0008414X00005824a.pdf, p. 976, Definition and Theorem 1.

import Definitions.Def_BirkhoffGlobalSection
import Mathlib.Analysis.Convex.Basic

namespace BirkhoffGlobalSection

open scoped Topology

/-- The local curvature step for a compact regular radial level set. The inward
side of a level set with positive tangential Hessian is locally convex. -/
theorem radial_filling_locally_convex_at_each_point
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
    ∀ x ∈ K, ∃ U : Set Phase, U ∈ 𝓝 x ∧ Convex ℝ (K ∩ U) := by sorry

end BirkhoffGlobalSection
