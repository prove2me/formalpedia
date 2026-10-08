-- Prove2me | Theorems.Thm_ChvatalArtGallery_FanPartition_cut_into_two_triangulations
-- name    : ChvatalArtGallery.FanPartition.cut_into_two_triangulations
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T08:58:18.540457+00:00
-- url     : https://prove2.me/theorems/c1d2c8f6-ccba-4bdc-b21e-9f7414c4e973
-- title:
--   Proof of the Theorem, p. 40 — the edge (j, j + k) cuts G into a (k + 1)-triangulation G₁ and an (n − k + 1)-triangulation G₂
-- statement:
--   Let $D$ be the set of inner edges of an $n$-triangulation $G$ with vertices $0,\dots,n-1$ in cyclic order (indices mod $n$), and let $\{j, j+k\} \in D$ be an inner edge with $2 \le k \le n-2$. Let
--   $$\iota_1 : \{0,\dots,k\} \to \{0,\dots,n-1\},\ i \mapsto j+i, \qquad \iota_2 : \{0,\dots,n-k\} \to \{0,\dots,n-1\},\ i \mapsto j+k+i,$$
--   and let $D_1$ (resp. $D_2$) be the set of diagonals of the $(k+1)$-gon (resp. the $(n-k+1)$-gon) whose image under $\iota_1$ (resp. $\iota_2$) lies in $D$. Then
--
--   1. $D_1$ is the set of inner edges of a $(k+1)$-triangulation $G_1$,
--   2. $D_2$ is the set of inner edges of an $(n-k+1)$-triangulation $G_2$, and
--   3. the triangles of $G$ are exactly the images under $\iota_1$ of the triangles of $G_1$ together with the images under $\iota_2$ of the triangles of $G_2$, and no triangle of $G$ arises in both ways.
--
--   In the paper this is the step "the edge $(j, j+k)$ cuts $G$ into a $(k+1)$-triangulation $G_1$ and an $(n-k+1)$-triangulation $G_2$": $G_1$ lies on the vertices $j, j+1, \dots, j+k$ and $G_2$ on $j+k, \dots, j+n = j$, and the cut edge is a side of both. It is what lets the induction combine a fan partition of $G_2$ (or of a slightly larger piece) with fans of $G_1$.
--
--   **Formalization Note.** The paper uses the cut for its particular $k$ ($4 \le k \le 6$, the least span of an inner edge); the statement is given for every inner edge $\{j, j+k\}$ with $2 \le k \le n-2$, which is the same fact and contains the paper's case. "Cuts $G$ into" is made explicit as the two pulled-back diagonal sets being triangulations and the triangles of $G$ being split between the two pieces. The pieces are relabelled $0,\dots,k$ and $0,\dots,n-k$ in the cyclic order inherited from $G$, so the cut edge becomes the side $\{k, 0\}$ of the first piece and the side $\{n-k, 0\}$ of the second. Triangles are transported by taking images of their vertex sets.
-- source:
--   Chvátal, A combinatorial theorem in plane geometry, J. Combin. Theory Ser. B 18 (1975), p. 40, proof of the Theorem, "The edge (j, j + k) cuts G into a (k + 1)-triangulation G1 and an (n − k + 1)-triangulation G2."

import Mathlib
import Definitions.Def_ChvatalArtGallery_FanPartition_Triangulation

namespace ChvatalArtGallery.FanPartition

/-- Proof of the Theorem, p. 40: an inner edge (j, j + k) cuts an n-triangulation into a
(k + 1)-triangulation G₁ on the vertices j, …, j + k and an (n − k + 1)-triangulation G₂ on the
vertices j + k, …, j + n = j, whose triangles together are exactly the triangles of G, with no
triangle in both. -/
theorem cut_into_two_triangulations (n : ℕ) (D : Finset (Sym2 (Fin n)))
    (hD : IsTriangulation n D) (j : Fin n) (k : ℕ) (hk2 : 2 ≤ k) (hkn : k ≤ n - 2)
    (hjk : s(j, shift j k) ∈ D) :
    let ι₁ : Fin (k + 1) → Fin n := arc j (k + 1)
    let ι₂ : Fin (n - k + 1) → Fin n := arc (shift j k) (n - k + 1)
    let D₁ := pullback ι₁ D
    let D₂ := pullback ι₂ D
    IsTriangulation (k + 1) D₁ ∧ IsTriangulation (n - k + 1) D₂ ∧
      Disjoint ((triangles (k + 1) D₁).image (fun T => T.image ι₁))
        ((triangles (n - k + 1) D₂).image (fun T => T.image ι₂)) ∧
      (triangles (k + 1) D₁).image (fun T => T.image ι₁) ∪
        (triangles (n - k + 1) D₂).image (fun T => T.image ι₂) = triangles n D := by sorry

end ChvatalArtGallery.FanPartition
