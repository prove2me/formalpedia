-- Prove2me | Theorems.Thm_BhangaleHypergraph_Main_avoiding_amplification
-- name    : BhangaleHypergraph.Main.avoiding_amplification
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T14:06:08.105995+00:00
-- url     : https://prove2.me/theorems/ddb7241b-59ed-4b83-a7a7-86c91ad90e6f
-- title:
--   Lemma 2.17 — Avoiding-set amplification
-- statement:
--   Let $C\ge2$, $s,R\ge1$, $U_{C,s}([R])\subseteq W\subseteq2^{[R]}$, and let $f:W\to[C]$ be admissible.
--
--   1. Some nonempty 1-avoiding set has size at most $C$.
--   2. For every color set $T$ with $|T|\le C-1$ and every $C+1$ pairwise disjoint $T$-avoiding sets $S_i$ of size at most $s$, there exist a color $b\notin T$ and a $(T\cup\{b\})$-avoiding set $S$ with
--   $$|S|\le(C-1)s+C.$$
--   The input $S_i$ and the output in the second clause are not required to be nonempty.
--
--   The theorem retains both local amplification conclusions.
--
--   Differences from the source:
--   - encoding: one-based finite label and color sets → zero-based Fin types and finite subsets; reason: subtracting one gives a bijection and preserves every instance
-- source:
--   Amey Bhangale, STOC 2027 submission #1052 (October 2026), Lemma 2.17, p. 12 (PDF p. 12); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1052.pdf

import Definitions.Def_BhangaleHypergraph_Main_Restricted

namespace BhangaleHypergraph.Main

theorem avoiding_amplification (C s R : ℕ) (hC : 2 ≤ C) (hs : 1 ≤ s) (hR : 1 ≤ R)
    (W : Finset (Finset (Fin R))) (hcore : Core C s R ⊆ W) (f : W → Fin C)
    (hf : Admissible f) :
    (∃ S : Finset (Fin R), S.Nonempty ∧ S.card ≤ C ∧ AvoidsNumber f S 1) ∧
    (∀ (T : Finset (Fin C)) (S : Fin (C + 1) → Finset (Fin R)),
      T.card ≤ C - 1 → (∀ i j, i ≠ j → Disjoint (S i) (S j)) →
      (∀ i, (S i).card ≤ s ∧ Avoids f (S i) T) →
      ∃ (b : Fin C) (U : Finset (Fin R)), b ∉ T ∧ U.card ≤ (C - 1) * s + C ∧
        Avoids f U (insert b T)) := by sorry

end BhangaleHypergraph.Main
