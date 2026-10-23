-- Prove2me | Theorems.Thm_BinaryExtForm_HypercubeRank_observation_2_3
-- name    : BinaryExtForm.HypercubeRank.observation_2_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T07:14:25.839452+00:00
-- url     : https://prove2.me/theorems/b20011c4-0cb5-4306-ae36-9e30f5db9124
-- title:
--   Observation 2.3, p. 4 — binary points of a binarization are unique per y and are vertices
-- statement:
--   Let $B \subseteq \mathbb R \times [0,1]^d$ be a binarization of the variable $x$ in the range $\{0, \dots, k\}$. Then for every $y \in \{0,1\}^d$:
--
--   1. there is at most one $x$ with $(x, y) \in B$;
--   2. if such an $x$ exists, then $x \in \{0, \dots, k\}$ and $(x, y)$ is a vertex of $B$.
--
--   So every $0/1$ vector $y$ encodes at most one value of $x$, that value lies in the range, and the corresponding binary point is a vertex of $B$.
--
--   **Formalization Note.** Points are `p : Fin (d+1) → ℝ` with $x$ = `p 0`. Part 1 says: if $p, q \in B$, $p$ has binary $y$-part and $q$ has the same $y$-part, then $q$ and $p$ have the same $x$.
-- source:
--   Aprile, Conforti, Di Summa, Binary extended formulations and sequential convexification, arXiv:2106.00354v1, p. 4, Observation 2.3

import Mathlib
import Definitions.Def_BinaryExtForm_HypercubeRank_Model

namespace BinaryExtForm.HypercubeRank
theorem observation_2_3 {d k : ℕ} (B : Set (Fin (d + 1) → ℝ)) (hB : IsBinarization d k B) :
    (∀ p ∈ B, ∀ q ∈ B, IsBinaryY p → yproj q = yproj p → q 0 = p 0) ∧
    (∀ p ∈ B, IsBinaryY p → (∃ m : ℕ, m ≤ k ∧ p 0 = m) ∧ p ∈ Set.extremePoints ℝ B) := by sorry
end BinaryExtForm.HypercubeRank
