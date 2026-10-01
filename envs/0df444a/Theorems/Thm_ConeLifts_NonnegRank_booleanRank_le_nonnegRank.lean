-- Prove2me | Theorems.Thm_ConeLifts_NonnegRank_booleanRank_le_nonnegRank
-- name    : ConeLifts.NonnegRank.booleanRank_le_nonnegRank
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T21:11:59.130996+00:00
-- url     : https://prove2.me/theorems/d8cb4dcd-dfc4-44f3-b117-94901979efee
-- title:
--   $\operatorname{rank}_B(M) \le \operatorname{rank}_+(M)$: nonnegative factorizations give Boolean factorizations of the support
-- statement:
--   Let $M = (M_{ij})$ be a nonnegative matrix with rows indexed by a set $I$ and columns by a set $J$, and let $k \in \mathbb{N}$. Suppose $M = AB$ with $A \in \mathbb{R}_+^{I \times k}$ and $B \in \mathbb{R}_+^{k \times J}$ nonnegative, that is,
--
--   $$M_{ij} = \sum_{l=1}^{k} A_{il} B_{lj} \qquad \text{for all } i \in I,\ j \in J .$$
--
--   Then the support $\operatorname{supp}(M)$ has a Boolean factorization of intermediate dimension $k$: there are $0/1$ matrices $A' \in \{0,1\}^{I \times k}$ and $B' \in \{0,1\}^{k \times J}$ with
--
--   $$M_{ij} \neq 0 \iff \exists\, l :\ A'_{il} = 1 \text{ and } B'_{lj} = 1 .$$
--
--   Since this holds for every $k$ admitting a nonnegative factorization, the Boolean rank of $\operatorname{supp}(M)$ is at most the nonnegative rank of $M$, $\operatorname{rank}_B(M) \le \operatorname{rank}_+(M)$ (including the case $\operatorname{rank}_+(M) = +\infty$). This is the step that transfers combinatorial lower bounds on the Boolean rank to the nonnegative rank.
--
--   **Formalization Note** The index sets are arbitrary types; the paper's $p \times q$ matrices are the case $I = [p]$, $J = [q]$, and the slack matrix of a polytope is the case $I = $ vertices, $J = $ facets. $0/1$ entries are `Bool`.
-- source:
--   Gouveia, Parrilo & Thomas, Lifts of Convex Sets and Cone Factorizations, arXiv:1111.3164v2, p. 15, §4.2 ("It is easy to see that rank_B(M) ≤ rank₊(M)"); Definition 4.10, p. 15; Definition 4.3 (1), p. 13

import Mathlib

namespace ConeLifts.NonnegRank

/-- Gouveia, Parrilo & Thomas, arXiv:1111.3164v2, §4.2, p. 15: "It is easy to see that
`rank_B(M) ≤ rank₊(M)`", stated in factorization form for every intermediate dimension `k` (so that
it also covers `rank₊(M) = +∞`): if the nonnegative matrix `M` factors as `M = AB` with `A` and `B`
nonnegative of intermediate dimension `k` (Definition 4.3 (1) with `K = (ℝⁱ₊)`, p. 13; Definition 3.2,
p. 9), then its support `supp(M)` (a one exactly where `M i j ≠ 0`) has a Boolean factorization
`supp(M) = A'B'` of intermediate dimension `k` in Boolean arithmetic (Definition 4.10, p. 15), with
`A'`, `B'` 0/1 matrices (entries in `Bool`).

The rows and columns are indexed by arbitrary types `ι`, `κ`; the paper's `p × q` matrices are
`ι = Fin p`, `κ = Fin q`, and the slack matrix of a polytope is indexed by its vertices and facets. -/
theorem booleanRank_le_nonnegRank {ι κ : Type*} (M : ι → κ → ℝ) (hM : ∀ i j, 0 ≤ M i j) (k : ℕ)
    (A : ι → Fin k → ℝ) (B : Fin k → κ → ℝ) (hA : ∀ i l, 0 ≤ A i l) (hB : ∀ l j, 0 ≤ B l j)
    (hAB : ∀ i j, M i j = ∑ l, A i l * B l j) :
    ∃ (A' : ι → Fin k → Bool) (B' : Fin k → κ → Bool),
      ∀ i j, (M i j ≠ 0 ↔ ∃ l, A' i l = true ∧ B' l j = true) := by sorry

end ConeLifts.NonnegRank
