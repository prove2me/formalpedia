-- Prove2me | Theorems.Thm_ConjugateConvex_Involution_eqOn_of_eqOn_intrinsicInterior
-- name    : ConjugateConvex.Involution.eqOn_of_eqOn_intrinsicInterior
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T14:25:01.050791+00:00
-- url     : https://prove2.me/theorems/efae551f-1252-4147-b1b0-949c1f8b450d
-- title:
--   §4, p. 76 — convex functions semi-continuous from below that agree at the interior points of G agree on G
-- statement:
--   Let $G \subseteq \mathbb R^n$ be convex and let $f$ and $g$ be two real functions that are convex on $G$ and semi-continuous from below on $G$. If $f(x) = g(x)$ at every relative-interior point $x$ of $G$, then
--
--   $$
--   f(x) = g(x) \quad \text{for every } x \in G,
--   $$
--
--   including the boundary points of $G$ that belong to $G$.
--
--   In the proof of the theorem this is applied to $f$ and the second conjugate $f^*$: after $f^* = f$ has been shown at the interior points, Fenchel concludes "as both functions are convex and semi-continuous from below, also at the boundary points of $G$". The statement names the two functions of that clause as arbitrary $f$, $g$; it is the principle the clause invokes, with nothing added.
--
--   **Formalization Note** Interior points are read as relative-interior points (`intrinsicInterior ℝ G`), as everywhere in the mission. Convexity and semi-continuity are taken on $G$ (`ConvexOn ℝ G`, `LowerSemicontinuousOn _ G`); values off $G$ play no role.
-- source:
--   Fenchel, On conjugate convex functions, Canad. J. Math. 1 (1949), p. 76, §4 ('as both functions are convex and semi-continuous from below, also at the boundary points of G')

import Mathlib

namespace ConjugateConvex.Involution

/-- Fenchel (1949), §4, p. 76, the clause "as both functions are convex and semi-continuous from
below, also at the boundary points of G": two functions convex and semi-continuous from below
on a convex set `G` that agree at the (relative) interior points of `G` agree on all of `G`. -/
theorem eqOn_of_eqOn_intrinsicInterior {n : ℕ} (G : Set (Fin n → ℝ)) (f g : (Fin n → ℝ) → ℝ)
    (hf : ConvexOn ℝ G f) (hg : ConvexOn ℝ G g)
    (hfl : LowerSemicontinuousOn f G) (hgl : LowerSemicontinuousOn g G)
    (hfg : Set.EqOn f g (intrinsicInterior ℝ G)) :
    Set.EqOn f g G := by sorry

end ConjugateConvex.Involution
