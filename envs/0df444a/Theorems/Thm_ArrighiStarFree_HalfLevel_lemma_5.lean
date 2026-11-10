-- Prove2me | Theorems.Thm_ArrighiStarFree_HalfLevel_lemma_5
-- name    : ArrighiStarFree.HalfLevel.lemma_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T18:06:26.492202+00:00
-- url     : https://prove2.me/theorems/3b23dd90-b741-492e-879a-d111765d2730
-- title:
--   Lemma 5 — shuffle-ideal concatenation, intersection and cyclic witnesses
-- statement:
--   Let $m\ge1$ and let $L_1,\ldots,L_m\subseteq\Sigma^*$ be arbitrary shuffle ideals over a finite alphabet. Let $a_1,\ldots,a_k$ enumerate that alphabet once, and let $\ell_i$ be the shortest word length in $L_i$, taking $\ell_i=0$ when $L_i$ is empty. The concatenation $L_1\cdots L_m$ is a shuffle ideal, and
--   $$\bigcap_{i=1}^m L_i\ne\varnothing\quad\Longleftrightarrow\quad L_1\cdots L_m\ne\varnothing\quad\Longleftrightarrow\quad\forall i,\ L_i\ne\varnothing.$$
--   In addition, for every $i$,
--   $$L_i\ne\varnothing\quad\Longleftrightarrow\quad(a_1\cdots a_k)^{\ell_i}\in L_i.$$
--
--   This structural milestone is stated for languages themselves, with no automaton presentation or supplied shortest witness. Empty languages, the universal language and shortest words of length zero are retained. Shuffle closure uses the literal factorization definition from the page; no characterization equivalence is assumed.
--
--   Differences from the source:
--   - encoding: languages indexed by 1 through m over a finite alphabet → an arbitrary finite alphabet type and a family indexed by Fin m, with 1 ≤ m; reason: zero-based indices change no language or instance
--   - encoding: the alphabet written as Σ={a₁,…,aₖ} and word powers → an exhaustive duplicate-free list and repeated list concatenation; reason: this makes the chosen order explicit, including the empty alphabet
--   - encoding: the shortest word length ℓᵢ in a nonempty language → the infimum of natural word lengths, with value zero on the empty language; reason: on nonempty languages it is the attained minimum; on the empty language both sides of the last equivalence remain false
-- source:
--   Arrighi et al. (2021), supplied source.pdf (arXiv:2110.01279v1), Lemma 5, printed p. 23:7, PDF p. 7

import Definitions.Def_ArrighiStarFree_HalfLevel_Words

namespace ArrighiStarFree.HalfLevel

theorem lemma_5 {α : Type*} [Fintype α] {m : ℕ} (hm : 1 ≤ m)
    (L : Fin m → Language α) (hL : ∀ i, ShuffleIdeal (L i))
    (alphabet : List α) (hnodup : alphabet.Nodup) (hcover : ∀ a, a ∈ alphabet) :
    ShuffleIdeal (LanguageProduct L) ∧
    ((LanguageIntersection L).Nonempty ↔ (LanguageProduct L).Nonempty) ∧
    ((LanguageProduct L).Nonempty ↔ ∀ i, (L i).Nonempty) ∧
    (∀ i, (L i).Nonempty ↔ cycleWord alphabet (shortestLength (L i)) ∈ L i) := by sorry

end ArrighiStarFree.HalfLevel
