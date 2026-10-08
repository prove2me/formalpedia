-- Prove2me | Theorems.Thm_ChvatalArtGallery_FanPartition_four_cases
-- name    : ChvatalArtGallery.FanPartition.four_cases
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T09:13:46.273405+00:00
-- url     : https://prove2.me/theorems/8c775649-b575-4cf7-a4eb-b24dca7b5577
-- title:
--   Proof of the Theorem, p. 40, cases (1)–(4) — G₁ is a fan or one of three configurations, up to mirror image
-- statement:
--   Let $4 \le k \le 6$ and let $D_1$ be the set of inner edges of a $(k+1)$-triangulation $G_1$ with vertices $0,1,\dots,k$ in cyclic order, so that $\{0,k\}$ is a side of $G_1$. Suppose that every inner edge $\{a,b\}$ of $G_1$ with $a<b$ satisfies $b-a \le 3$. Then one of the following holds:
--
--   1. $G_1$ is a fan;
--   2. $k = 5$ and the inner edges of $G_1$ are $\{0,2\}, \{0,3\}, \{3,5\}$;
--   3. $k = 6$ and the inner edges of $G_1$ are $\{0,2\}, \{0,3\}, \{3,6\}, \{4,6\}$;
--   4. $k = 6$ and the inner edges of $G_1$ are $\{0,3\}, \{1,3\}, \{3,6\}, \{4,6\}$;
--
--   or the mirror image of $G_1$ under $i \mapsto k-i$ is as in (2) or (4).
--
--   In the paper $G_1$ is the piece cut off by the inner edge $(j, j+k)$ of least span $k\ge4$, its vertex $i$ is the paper's $j+i$, and the hypothesis on spans is the minimality of $k$: an inner edge $\{a,b\}$ of $G_1$ with $4 \le b-a$ would be an edge $(j+a, j+b)$ of $G$ of span $b - a < k$. The four cases drive the four inductive constructions that close the proof.
--
--   **Formalization Note.** "It is easy to verify that we have one of the following four cases (or perhaps a mirror image of (2) or (4))" is stated as an explicit disjunction on the diagonal set $D_1$ of $G_1$ in its own labelling $0,\dots,k$; the paper's $(j+a, j+b)$ is written $\{a,b\}$. The mirror image is the relabelling $i \mapsto k-i$ (`Fin.rev`), applied to $D_1$; case (3) is its own mirror image. The minimality of $k$ enters only through the span hypothesis. The vertex numerals are elements of `Fin (k+1)`; each configuration is asserted only together with the value of $k$ it is printed with. "$G_1$ is a fan" is `IsFan (k+1) D₁ (triangles (k+1) D₁)`.
-- source:
--   Chvátal, A combinatorial theorem in plane geometry, J. Combin. Theory Ser. B 18 (1975), p. 40, proof of the Theorem, cases (1)–(4) ("It is easy to verify that we have one of the following four cases (or perhaps a mirror image of (2) or (4)).")

import Mathlib
import Definitions.Def_ChvatalArtGallery_FanPartition_Triangulation

namespace ChvatalArtGallery.FanPartition

/-- Proof of the Theorem, p. 40, cases (1)–(4): a (k + 1)-triangulation G₁ (4 ≤ k ≤ 6, vertices
0, …, k, cut edge (0, k) on its boundary) all of whose inner edges (a, b), a < b, have b − a ≤ 3
is a fan, or is one of the configurations (2), (3), (4), or the mirror image (i ↦ k − i) of (2)
or (4). -/
theorem four_cases (k : ℕ) (hk4 : 4 ≤ k) (hk6 : k ≤ 6) (D₁ : Finset (Sym2 (Fin (k + 1))))
    (hD₁ : IsTriangulation (k + 1) D₁)
    (hspan : ∀ a b : Fin (k + 1), a < b → s(a, b) ∈ D₁ → b.val - a.val ≤ 3) :
    IsFan (k + 1) D₁ (triangles (k + 1) D₁) ∨
    (k = 5 ∧ (D₁ = {s(0, 2), s(0, 3), s(3, 5)} ∨
      D₁.image (Sym2.map Fin.rev) = {s(0, 2), s(0, 3), s(3, 5)})) ∨
    (k = 6 ∧ D₁ = {s(0, 2), s(0, 3), s(3, 6), s(4, 6)}) ∨
    (k = 6 ∧ (D₁ = {s(0, 3), s(1, 3), s(3, 6), s(4, 6)} ∨
      D₁.image (Sym2.map Fin.rev) = {s(0, 3), s(1, 3), s(3, 6), s(4, 6)})) := by sorry

end ChvatalArtGallery.FanPartition
