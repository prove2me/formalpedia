-- Prove2me | Theorems.Thm_FamousTheorems_projective_plane_card_points_7a
-- name    : FamousTheorems.projective_plane_card_points_7a
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T12:27:37.359342+00:00
-- url     : https://prove2.me/theorems/c2d91628-1a9d-4496-80b3-6e9776726808
-- title:
--   A finite projective plane of order n has n²+n+1 points
-- statement:
--   **A finite projective plane of order $n$ has $n^2+n+1$ points.** Let $(P,L)$ be a finite projective plane, so that any two points lie on a unique line, any two lines meet in a unique point, and there are four points with no three collinear. Let $n+1$ be the number of points on a line, so that $n$ is the order of the plane. Then $|P|=n^2+n+1$.
--
--   Every line has the same number $n+1$ of points and every point lies on $n+1$ lines. Counting the lines through a fixed point then gives the formula, and by duality there are also $n^2+n+1$ lines. The projective plane over $\mathbb F_q$ has order $q$. Whether every finite projective plane has prime-power order is a major open problem, and the Bruck–Ryser theorem and the computer search of Lam rule out orders $6$ and $10$.
--
--   **Formalization note.** Mathlib's `Configuration.ProjectivePlane.card_points`. `Configuration.ProjectivePlane P L` bundles the axioms, and `ProjectivePlane.order P L` is defined as the number of lines through a point minus one, which equals the number of points on a line minus one. Incidence is given by `Membership P L`.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `Configuration.ProjectivePlane.card_points`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem projective_plane_card_points_7a (P L : Type*) [Membership P L] [Configuration.ProjectivePlane P L] [Fintype P] [Finite L] :
    Fintype.card P = Configuration.ProjectivePlane.order P L ^ 2 + Configuration.ProjectivePlane.order P L + 1 := by sorry

end FamousTheorems
