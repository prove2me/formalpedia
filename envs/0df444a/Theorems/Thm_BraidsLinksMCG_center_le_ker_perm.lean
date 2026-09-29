-- Prove2me | Theorems.Thm_BraidsLinksMCG_center_le_ker_perm
-- name    : BraidsLinksMCG.center_le_ker_perm
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-21T20:47:05.287374+00:00
-- url     : https://prove2.me/theorems/fdb18028-e64f-41cb-b196-e38a2ae6e748
-- title:
--   Central braids are pure
-- statement:
--   For $n \ge 3$, every central braid is pure: the centre of the braid group is contained in the kernel of the underlying-permutation homomorphism,
--
--   $$Z(B_n) \;\le\; \ker\bigl(\pi : B_n \to \mathfrak{S}_n\bigr).$$
--
--   Equivalently, a braid that commutes with every braid must return each strand to its own starting position.
--
--   The proof has two halves, both elementary, and the hypothesis $n \ge 3$ enters only in the second.
--
--   First, $\pi$ is surjective. Its values on the Artin generators are the adjacent transpositions, and those generate the symmetric group, so the image is everything. Surjectivity is what lets centrality be transported: if $b$ is central in $B_n$ then $\pi(b)$ commutes with $\pi(a)$ for every $a$, and every element of $\mathfrak{S}_n$ is such a $\pi(a)$, so $\pi(b)$ is central in $\mathfrak{S}_n$.
--
--   Second, the symmetric group on at least three letters has trivial centre. Suppose $s$ is central and $s(a) \ne a$. Because there are at least three letters, choose $c$ distinct from both $a$ and $s(a)$, and commute $s$ past the transposition of $s(a)$ and $c$. Evaluating both sides at $a$ gives $c$ on one side and $s(a)$ on the other, contradicting the choice of $c$. Hence $s$ fixes everything.
--
--   Combining, $\pi(b)$ is trivial, which is the claim.
--
--   The hypothesis $n \ge 3$ is necessary and not an artefact: $B_1$ and $B_2$ are abelian, so their centres are the whole group, while $\pi$ is onto $\mathfrak{S}_2$ for $n = 2$ and the generator $\sigma_1$ is both central and a transposition. So for $n = 2$ the conclusion fails outright.
--
--   The use of this is to narrow the computation of the centre. Corollario 1.8.4 asserts $Z(B_n) = \langle \Delta^2 \rangle$; the containment $\langle \Delta^2 \rangle \le Z(B_n)$ is already proved on the platform, and the reverse containment is the open direction. This lemma shows that in attacking it one may assume from the start that the central braid under consideration is pure, which is exactly the hypothesis under which the pure braid machinery --- combing, the semidirect decomposition --- becomes available.
-- source:
--   Birman, Braids, Links and Mapping Class Groups, Chapter 1, Corollary 1.8.4; the symmetric group input is the standard triviality of the centre of the symmetric group on at least three letters.

import Mathlib
import Definitions.Def_BraidsLinksMCG_ArtinBraidGroup
import Definitions.Def_BraidsLinksMCG_ArtinEndo

namespace BraidsLinksMCG

theorem center_le_ker_perm (n : ℕ) (hn : 3 ≤ n)
    (pi : ArtinBraidGroup n →* Equiv.Perm (Fin n))
    (hpi : ∀ i : Fin (n - 1), pi (sigma i) = Equiv.swap (strandIdx i) (strandIdxSucc i)) :
    Subgroup.center (ArtinBraidGroup n) ≤ pi.ker := by sorry

end BraidsLinksMCG
