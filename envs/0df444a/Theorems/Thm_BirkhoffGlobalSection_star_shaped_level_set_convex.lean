-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_star_shaped_level_set_convex
-- name    : BirkhoffGlobalSection.star_shaped_level_set_convex
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-09-26T18:37:21.903374+00:00
-- url     : https://prove2.me/theorems/fc05791e-84dc-429b-8757-5f5f34b7689a
-- title:
--   Star-shaped zero level with positive tangential Hessian bounds a convex region (Hadamard)
-- statement:
--   Let $F:\mathbb R^4\to\mathbb R$ and let $S\subset\mathbb R^4$ be compact. Assume:
--
--   1. $F=0$ on $S$, and $\nabla F(s)\ne0$ for every $s\in S$;
--   2. $F$ has **positive tangential Hessian** on $S$: $F$ is $C^2$ at each $s\in S$, and $D^2F(s)(v,v)>0$ for every nonzero $v$ with $DF(s)[v]=0$;
--   3. $S$ is a **radial graph over the unit sphere**: for every unit vector $x\in S^3$ there is exactly one $r>0$ with $r x\in S$;
--   4. $F<0$ **strictly inside** along each ray: if $Rx\in S$ with $R>0$, then $F(rx)<0$ for all $0\le r<R$.
--
--   Then the region enclosed by $S$,
--
--   $$
--   \widehat S=\{\,t\,s:\ s\in S,\ 0\le t\le1\,\},
--   $$
--
--   is convex.
--
--   This is the classical theorem that a compact hypersurface with positive definite second fundamental form bounds a convex body (Hadamard's ovaloid theorem). Here it is stated in the form needed for energy surfaces given as zero levels of a Hamiltonian that are star-shaped with respect to the origin. The hypotheses fix the orientation: $F$ increases outward, and positivity of the tangential Hessian of $F$ says the level set curves toward the region $\{F<0\}$.
--
--   **Formalization Note.** $\mathbb R^4$ is `Phase` $=\mathrm{Fin}\,4\to\mathbb R$, rays are written $(r x_i)_i$ for $x$ in the round unit sphere `unitThreeSphere`, and the tangential-Hessian hypothesis is the platform predicate `HasPositiveTangentialHessianOn`.
-- source:
--   J. Hadamard, Sur certaines propriétés des trajectoires en dynamique, J. Math. Pures Appl. (5) 3 (1897) 331–387 (ovaloid theorem: positive definite second fundamental form implies boundary of a convex body); local-to-global convexity: H. Tietze, Über Konvexheit im kleinen und im großen, Math. Z. 28 (1928), and S. Nakajima, Tôhoku Math. J. 29 (1928). Used in Joung–van Koert, https://arxiv.org/abs/2407.19159v3, Theorem 1.5 / Proposition 4.4 (convexity from positive curvature).

import Definitions.Def_BirkhoffGlobalSection
import Mathlib.Analysis.Convex.Basic

namespace BirkhoffGlobalSection

/-- Hadamard-type convexity: a compact star-shaped zero level of `F` with nonzero gradient,
positive tangential Hessian, and `F < 0` strictly inside along every ray, bounds a convex
region (the union of the segments from the origin to its points). -/
theorem star_shaped_level_set_convex (F : Phase → ℝ) (S : Set Phase)
    (hS : IsCompact S)
    (hF0 : ∀ s ∈ S, F s = 0)
    (hreg : ∀ s ∈ S, fderiv ℝ F s ≠ 0)
    (hTH : HasPositiveTangentialHessianOn F S)
    (hray : ∀ x ∈ unitThreeSphere, ∃ r : ℝ, 0 < r ∧ (fun i : Fin 4 => r * x i) ∈ S)
    (huniq : ∀ x ∈ unitThreeSphere, ∀ r t : ℝ, 0 < r → 0 < t →
      (fun i : Fin 4 => r * x i) ∈ S → (fun i : Fin 4 => t * x i) ∈ S → r = t)
    (hneg : ∀ x ∈ unitThreeSphere, ∀ R : ℝ, 0 < R → (fun i : Fin 4 => R * x i) ∈ S →
      ∀ r : ℝ, 0 ≤ r → r < R → F (fun i : Fin 4 => r * x i) < 0) :
    Convex ℝ {y : Phase | ∃ s ∈ S, ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ y = t • s} := by sorry

end BirkhoffGlobalSection
