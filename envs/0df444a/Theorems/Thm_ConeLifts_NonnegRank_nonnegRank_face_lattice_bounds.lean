-- Prove2me | Theorems.Thm_ConeLifts_NonnegRank_nonnegRank_face_lattice_bounds
-- name    : ConeLifts.NonnegRank.nonnegRank_face_lattice_bounds
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T21:14:22.237988+00:00
-- url     : https://prove2.me/theorems/58773c7f-60b9-4599-976a-c95e73081da8
-- title:
--   Corollary 4.13 — antichain and Goemans lower bounds on the nonnegative rank of a polytope
-- statement:
--   Let $C \subseteq \mathbb{R}^n$ be a polytope with the origin in its interior, and let $\operatorname{rank}_+(C)$ be its nonnegative rank. Then:
--
--   1. **(Antichain bound.)** Let $p$ be the size of an antichain of faces of $C$, i.e. a set of faces no one of which is contained in another. Then $\operatorname{rank}_+(C)$ is at least the smallest $k$ such that
--   $$p \le \binom{k}{\lfloor k/2 \rfloor} .$$
--   2. **(Goemans.)** Let $n_C$ be the number of faces of $C$. Then
--   $$\operatorname{rank}_+(C) \ \ge\ \log_2 (n_C) .$$
--
--   For a square, $n_C = 10$ and the largest antichain has $4$ faces, giving $\operatorname{rank}_+ \ge \log_2 10 \approx 3.32$ and $\operatorname{rank}_+ \ge 4$; for the three-dimensional cube, $n_C = 28$ and the $12$ edges form an antichain, giving $\log_2 28 \approx 4.81$ and $6$. These are the classical combinatorial lower bounds on the size of a linear-programming lift of a polytope.
--
--   **Formalization Note** Faces are exposed faces, including $\emptyset$ and $C$. Part 1 is stated for every antichain of faces rather than a largest one; this is equivalent, since the bound is monotone in $p$ and a largest antichain is among them. The smallest $k$ is written as `sInf` of a set that is nonempty because central binomial coefficients are unbounded. Part 2 is stated as: for every $k \in \mathbb{N}$ with $\operatorname{rank}_+(C) = k$, $\log_2 n_C \le k$; when $\operatorname{rank}_+(C) = +\infty$ the bound holds trivially. $n_C$ is `Nat.card` of the type of faces, which is finite for a polytope; $\log_2$ is `Real.logb 2`.
-- source:
--   Gouveia, Parrilo & Thomas, Lifts of Convex Sets and Cone Factorizations, arXiv:1111.3164v2, p. 16, Corollary 4.13

import Mathlib
import Definitions.Def_ConeLifts_NonnegRank_IsPolytope
import Definitions.Def_ConeLifts_NonnegRank_Face
import Definitions.Def_ConeLifts_NonnegRank_nonnegRank

namespace ConeLifts.NonnegRank

/-- **Corollary 4.13** (Gouveia, Parrilo & Thomas, arXiv:1111.3164v2, p. 16). If `C ⊆ ℝⁿ` is a
polytope (with the origin in its interior), then:

1. (antichain bound) if `p` is the size of an antichain of faces of `C` (no face of the family is
   contained in another), `rank₊(C)` is at least the smallest `k` with `p ≤ (k choose ⌊k/2⌋)`;
   stated for every antichain, which is equivalent to the paper's "largest antichain" because the
   bound is monotone in `p` and a largest antichain is one of them;
2. (Goemans) if `n_C` is the number of faces of `C`, then `rank₊(C) ≥ log₂ n_C`; stated for every
   finite value `k` of `rank₊(C)`, the case `rank₊(C) = +∞` being trivially true.

Faces are exposed faces, including `∅` and `C`; a polytope has finitely many, so `Nat.card` is the
face count. The set `{k | p ≤ (k choose ⌊k/2⌋)}` is nonempty (central binomials are unbounded), so
its `sInf` is its minimum. -/
theorem nonnegRank_face_lattice_bounds {n : ℕ} (C : Set (EuclideanSpace ℝ (Fin n)))
    (hC : IsPolytope C) :
    (∀ 𝒜 : Finset (Face C), IsAntichain (· ≤ ·) (𝒜 : Set (Face C)) →
        ((sInf {k : ℕ | 𝒜.card ≤ k.choose (k / 2)} : ℕ) : ℕ∞) ≤ nonnegRank C) ∧
    (∀ k : ℕ, (k : ℕ∞) = nonnegRank C → Real.logb 2 (Nat.card (Face C) : ℝ) ≤ k) := by sorry

end ConeLifts.NonnegRank
