-- Prove2me | Theorems.Thm_BinaryExtForm_HypercubeRank_Supplement_theorem_3_1
-- name    : BinaryExtForm.HypercubeRank.Supplement.theorem_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T04:00:19.109793+00:00
-- url     : https://prove2.me/theorems/958119b3-4d37-474d-86f0-5396c8d82e90
-- title:
--   Theorem 3.1, p. 6 — vertices of a binary extended formulation with natural binarizations
-- statement:
--   Let $P \subseteq [0,k]^p \times \mathbb R^{n-p}$ be a polytope, where $k$ is a positive integer, and let $Q \subseteq \mathbb R^n \times [0,1]^{pd}$ be the binary extended formulation of $P$ with binarizations $B_1, \dots, B_p \subseteq \mathbb R \times [0,1]^d$ of $x_1, \dots, x_p$ in the range $\{0,\dots,k\}$. Assume every $B_i$ is **natural**: $x_i$ is an integer at every vertex of $B_i$. For $(\bar x, \bar y) \in \mathbb R^n \times [0,1]^{pd}$ write $\bar y_i = (\bar y_{i1}, \dots, \bar y_{id})$. Then $(\bar x, \bar y)$ is a vertex of $Q$ if and only if there exist a set $I \subseteq [p]$, a vector $\alpha \in \{0, \dots, k\}^I$ and a face $F$ of $P$ of dimension $|I|$ such that
--
--   1. $F \cap G_{I,\alpha} = \{\bar x\}$, where $G_{I,\alpha} = \{x \in \mathbb R^n : x_i = \alpha_i\ \forall i \in I\}$;
--   2. $(\bar x_i, \bar y_i)$ is a vertex of $B_i$ for every $i \in I$;
--   3. $(\bar x_i, \bar y_i)$ is a vertex of the slice $B_i \cap \{x_i = \bar x_i\}$ for every $i \in [p] \setminus I$.
--
--   In symbols,
--   $$(\bar x, \bar y) \in V(Q) \iff \exists\, I, \alpha, F:\ \dim F = |I|,\ F \cap G_{I,\alpha} = \{\bar x\},\ (\bar x_i,\bar y_i) \in \begin{cases} V(B_i) & i \in I,\\ V(B_i \cap \{x_i = \bar x_i\}) & i \notin I.\end{cases}$$
--
--   The theorem describes the vertices of $Q$ in terms of faces of the original polytope $P$ and vertices of the individual binarizations. Theorem 3.2 projects it to the $x$-space, and the proof of Theorem 4.6 uses it to relate the fractional vertices of $Q$ to slices of a single binarization. Remark 3.3 of the paper shows that naturality cannot be dropped.
--
--   **Formalization Note.** Points of $Q$ are pairs `(x, y)` with `y : Fin p → Fin d → ℝ` (0-based), and the binarized coordinates are the first $p$ of `Fin n`. A face is a convex extreme subset of $P$ and its dimension is the `finrank` of its `vectorSpan`. The vector $\alpha$ is a function `Fin p → ℕ` whose values on $I$ are at most $k$; values off $I$ play no role.
--
--   Differences from the source:
--   - encoding: points of ℝ^n × [0,1]^{pd}, faces of P, their dimension, α ∈ {0,…,k}^I → `(Fin n → ℝ) × (Fin p → Fin d → ℝ)` with 0-based indices, `Convex ℝ F ∧ IsExtreme ℝ P F`, `finrank (vectorSpan ℝ F)`, `α : Fin p → ℕ` with `α i ≤ k` for `i ∈ I`; reason: Lean conventions that change no instance (convex extreme subsets of a polytope are its faces; values of α off I are unused)
-- source:
--   Aprile, Conforti, Di Summa, Binary extended formulations and sequential convexification, arXiv:2106.00354v1, p. 6, Theorem 3.1

import Mathlib
import Definitions.Def_BinaryExtForm_HypercubeRank_Model
import Definitions.Def_BinaryExtForm_HypercubeRank_Supplement_Formulation

namespace BinaryExtForm.HypercubeRank.Supplement
open BinaryExtForm.HypercubeRank
theorem theorem_3_1 {n p d k : ℕ} (hpn : p ≤ n) (P : Set (Fin n → ℝ)) (hP : IsPolytope P)
    (hPk : ∀ x ∈ P, ∀ i : Fin p, 0 ≤ xc hpn x i ∧ xc hpn x i ≤ k)
    (B : Fin p → Set (Fin (d + 1) → ℝ)) (hB : ∀ i, IsBinarization d k (B i))
    (hN : ∀ i, IsNatural (B i))
    (xbar : Fin n → ℝ) (ybar : Fin p → Fin d → ℝ) (hy : ∀ i j, 0 ≤ ybar i j ∧ ybar i j ≤ 1) :
    (xbar, ybar) ∈ Set.extremePoints ℝ (BEF hpn P B) ↔
      ∃ (I : Finset (Fin p)) (α : Fin p → ℕ) (F : Set (Fin n → ℝ)),
        (∀ i ∈ I, α i ≤ k) ∧ IsFace P F ∧ affDim F = I.card ∧
        F ∩ G hpn I α = {xbar} ∧
        (∀ i ∈ I, block hpn (xbar, ybar) i ∈ Set.extremePoints ℝ (B i)) ∧
        (∀ i ∉ I, block hpn (xbar, ybar) i ∈
          Set.extremePoints ℝ (slice (B i) (xc hpn xbar i))) := by sorry
end BinaryExtForm.HypercubeRank.Supplement
