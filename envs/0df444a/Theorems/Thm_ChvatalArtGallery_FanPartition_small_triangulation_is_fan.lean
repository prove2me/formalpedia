-- Prove2me | Theorems.Thm_ChvatalArtGallery_FanPartition_small_triangulation_is_fan
-- name    : ChvatalArtGallery.FanPartition.small_triangulation_is_fan
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T08:57:42.777333+00:00
-- url     : https://prove2.me/theorems/d511df8e-59d1-4af6-80d8-b9441a1c7ecc
-- title:
--   Proof of the Theorem, p. 40 — every n-triangulation with n ≤ 5 is a fan
-- statement:
--   Let $3 \le n \le 5$ and let $D$ be the set of inner edges of an $n$-triangulation $G$ (vertices $0,\dots,n-1$ in cyclic order). Then the set of all triangles of $G$ is a fan: there is a vertex of $G$ meeting every inner edge of $G$,
--   $$\exists\, c,\ \forall\, e \in D,\ c \in e,$$
--   and, the triangles of $G$ being dual-connected, $G$ itself is a single fan.
--
--   This is the base case of Chvátal's induction on $n$: for $n \le 5$ the trivial partition $\{G\}$ consists of $1 = \lfloor n/3\rfloor$ fan.
--
--   **Formalization Note.** $G$ is encoded by the maximal non-crossing diagonal set $D$ of the $n$-gon; "$G$ is a fan" is stated as `IsFan n D (triangles n D)`, i.e. the whole set of triangles is nonempty, dual-connected and has a centre on all of its inner edges (which are exactly the members of $D$). The range $3 \le n \le 5$ is the paper's "$n = 3, 4, 5$"; for $n = 6$ the statement fails (the triangulation with diagonals $\{0,2\},\{2,4\},\{4,0\}$ is not a fan).
-- source:
--   Chvátal, A combinatorial theorem in plane geometry, J. Combin. Theory Ser. B 18 (1975), p. 40, proof of the Theorem, "The cases n = 3, 4, 5 are trivial as each n-triangulation with n ≤ 5 is a fan."

import Mathlib
import Definitions.Def_ChvatalArtGallery_FanPartition_Triangulation

namespace ChvatalArtGallery.FanPartition

/-- Proof of the Theorem, p. 40: every n-triangulation with 3 ≤ n ≤ 5 is a fan. -/
theorem small_triangulation_is_fan (n : ℕ) (hn3 : 3 ≤ n) (hn5 : n ≤ 5)
    (D : Finset (Sym2 (Fin n))) (hD : IsTriangulation n D) :
    IsFan n D (triangles n D) := by sorry

end ChvatalArtGallery.FanPartition
