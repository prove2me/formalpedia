-- Prove2me | Theorems.Thm_CycleLengthsExp_BetaGraph_large_set_nbhd
-- name    : CycleLengthsExp.BetaGraph.large_set_nbhd
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T21:24:28.770361+00:00
-- url     : https://prove2.me/theorems/978336ce-d32c-46e3-b04f-7e83153b6618
-- title:
--   p. 16 — large sets in H: fewer than βn vertices of H miss U ∪ N_H(U), so |N_H(U)| > (1−4β)n for βn ≤ |U| ≤ 2βn
-- statement:
--   Let $\beta>0$, let $G$ be a β-graph on $n$ vertices, and let $H=G[S]$ be an induced subgraph with the size and small-set expansion properties of Lemma 4.1. Then:
--
--   1. for every $U\subseteq V(H)$ with $|U|\ge\beta n$,
--   $$|V(H)\setminus(U\cup N_H(U))|<\beta n;$$
--   2. in particular, for every $U\subseteq V(H)$ with $\beta n\le|U|\le 2\beta n$,
--   $$|N_H(U)|\ >\ |V(H)|-|U|-\beta n\ \ge\ (1-4\beta)\,n.$$
--
--   Together with Lemma 4.1 this gives the two expansion conditions of Theorem 4.1 for the subgraph $H$: Lemma 4.1 controls small sets, this statement the sets of size between $\beta n$ and $2\beta n$.
--
--   **Formalization Note** The hypotheses on $H$ are $|S|\ge(1-\beta)n$ and $|N_H(U)|\ge\frac{1-3\beta}{2\beta}|U|$ for every $U\subseteq S$ of size at most $\beta n$, as supplied by Lemma 4.1. The latter hypothesis is not needed for this particular deduction. $N_H(U)$ is written $N_G(U)\cap S$.
-- source:
--   Friedman and Krivelevich, Cycle lengths in expanding graphs, arXiv:1912.11011v2, p. 16, proof of Theorem 3, second paragraph ("Moreover, if |U| ≥ βn …")

import Mathlib
import Definitions.Def_CycleLengthsExp_BetaGraph_Setting

namespace CycleLengthsExp.BetaGraph

/-- The large-set property of `H = G[S]` (p. 16): for the large expanding subgraph supplied
by Lemma 4.1, every `U ⊆ S` with `|U| ≥ βn` leaves fewer than `βn`
vertices of `S` outside `U ∪ N_H(U)`, and every `U ⊆ S` with `βn ≤ |U| ≤ 2βn` has
`|N_H(U)| > (1 - 4β)n`. Here `N_H(U) = N_G(U) ∩ S`. -/
theorem large_set_nbhd (β : ℝ) (hβ : 0 < β) (n : ℕ) (G : SimpleGraph (Fin n))
    (hG : IsBetaGraph β G) (S : Set (Fin n)) (hS : (1 - β) * n ≤ S.ncard)
    (hSexp : ∀ U ⊆ S, (U.ncard : ℝ) ≤ β * n →
      (1 - 3 * β) / (2 * β) * U.ncard ≤ (CycleLengthsExp.WellSpread.extNbhd G U ∩ S).ncard) :
    (∀ U ⊆ S, β * n ≤ U.ncard →
        ((S \ (U ∪ (CycleLengthsExp.WellSpread.extNbhd G U ∩ S))).ncard : ℝ) < β * n) ∧
    (∀ U ⊆ S, β * n ≤ U.ncard → (U.ncard : ℝ) ≤ 2 * β * n →
        (1 - 4 * β) * n < (CycleLengthsExp.WellSpread.extNbhd G U ∩ S).ncard) := by sorry

end CycleLengthsExp.BetaGraph
