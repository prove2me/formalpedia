-- Prove2me | Theorems.Thm_BinaryExtForm_HypercubeRank_Supplement_theorem_3_2
-- name    : BinaryExtForm.HypercubeRank.Supplement.theorem_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T04:00:55.380191+00:00
-- url     : https://prove2.me/theorems/c53cef60-bbf3-431a-969e-13a72278e1fd
-- title:
--   Theorem 3.2, p. 6 — π_x(V(Q)) consists of the points with F ∩ G_{I,α} = {x̄} for a face F of P of dimension |I|
-- statement:
--   Let $P \subseteq [0,k]^p \times \mathbb R^{n-p}$ be a polytope, $k$ a positive integer, and let $Q$ be the binary extended formulation of $P$ with binarizations $B_1, \dots, B_p \subseteq \mathbb R \times [0,1]^d$ of $x_1, \dots, x_p$ in the range $\{0,\dots,k\}$, all of them natural. Write $\pi_x(V(Q))$ for the set of $x$-parts $\bar x$ of the vertices $(\bar x, \bar y)$ of $Q$. Then a point $\bar x \in \mathbb R^n$ belongs to $\pi_x(V(Q))$ if and only if there exist a set $I \subseteq [p]$, a vector $\alpha \in \{0, \dots, k\}^I$ and a face $F$ of $P$ of dimension $|I|$ such that
--   $$F \cap G_{I,\alpha} = \{\bar x\}, \qquad G_{I,\alpha} = \{x \in \mathbb R^n : x_i = \alpha_i\ \forall i \in I\}.$$
--
--   The result describes the projections of the vertices of the extended formulation in the original space without reference to the binarizations: they depend only on $P$ and the range $\{0,\dots,k\}$. Remark 3.3 of the paper shows that naturality cannot be dropped.
--
--   **Formalization Note.** $\pi_x(V(Q))$ is `Prod.fst '' Set.extremePoints ℝ (BEF hpn P B)`. Faces, dimension and $\alpha$ are encoded as in Theorem 3.1.
--
--   Differences from the source:
--   - encoding: points, faces of P, their dimension, α ∈ {0,…,k}^I → `(Fin n → ℝ) × (Fin p → Fin d → ℝ)`, `Convex ℝ F ∧ IsExtreme ℝ P F`, `finrank (vectorSpan ℝ F)`, `α : Fin p → ℕ` with `α i ≤ k` for `i ∈ I`; reason: Lean conventions that change no instance
-- source:
--   Aprile, Conforti, Di Summa, Binary extended formulations and sequential convexification, arXiv:2106.00354v1, p. 6, Theorem 3.2

import Mathlib
import Definitions.Def_BinaryExtForm_HypercubeRank_Model
import Definitions.Def_BinaryExtForm_HypercubeRank_Supplement_Formulation

namespace BinaryExtForm.HypercubeRank.Supplement
open BinaryExtForm.HypercubeRank
theorem theorem_3_2 {n p d k : ℕ} (hpn : p ≤ n) (P : Set (Fin n → ℝ)) (hP : IsPolytope P)
    (hPk : ∀ x ∈ P, ∀ i : Fin p, 0 ≤ xc hpn x i ∧ xc hpn x i ≤ k)
    (B : Fin p → Set (Fin (d + 1) → ℝ)) (hB : ∀ i, IsBinarization d k (B i))
    (hN : ∀ i, IsNatural (B i)) (xbar : Fin n → ℝ) :
    xbar ∈ Prod.fst '' Set.extremePoints ℝ (BEF hpn P B) ↔
      ∃ (I : Finset (Fin p)) (α : Fin p → ℕ) (F : Set (Fin n → ℝ)),
        (∀ i ∈ I, α i ≤ k) ∧ IsFace P F ∧ affDim F = I.card ∧
        F ∩ G hpn I α = {xbar} := by sorry
end BinaryExtForm.HypercubeRank.Supplement
