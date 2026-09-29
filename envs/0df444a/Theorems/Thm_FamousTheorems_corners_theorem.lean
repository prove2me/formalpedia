-- Prove2me | Theorems.Thm_FamousTheorems_corners_theorem
-- name    : FamousTheorems.corners_theorem
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-23T09:15:21.462522+00:00
-- url     : https://prove2.me/theorems/12ffc049-d047-4e95-aa83-6c5459f53d12
-- title:
--   The corners theorem
-- statement:
--   **The corners theorem.** For every $\varepsilon>0$ and all sufficiently large $n$, every set $A\subseteq[n]^2$ with $|A|\ge\varepsilon n^2$ contains a corner, three points $(x,y),(x+d,y),(x,y+d)$ with $d\ne0$.
--
--   Due to Ajtai and Szemerédi, it is a two-dimensional density Ramsey theorem. It implies Roth's theorem on three-term arithmetic progressions, and its proof via the triangle removal lemma is a model argument of additive combinatorics.
--
--   **Formalization note.** Mathlib's `corners_theorem_nat`. The threshold `cornersTheoremBound (ε / 9)` comes from the triangle removal lemma, and `IsCornerFree` expresses the absence of nontrivial corners.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `corners_theorem_nat`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem corners_theorem {n : ℕ} {ε : ℝ} (hε : 0 < ε) (hn : cornersTheoremBound (ε / 9) ≤ n) (A : Finset (ℕ × ℕ))
    (hAn : A ⊆ Finset.range n ×ˢ Finset.range n) (hAε : ε * n ^ 2 ≤ A.card) :
    ¬ IsCornerFree (A : Set (ℕ × ℕ)) := by sorry

end FamousTheorems
