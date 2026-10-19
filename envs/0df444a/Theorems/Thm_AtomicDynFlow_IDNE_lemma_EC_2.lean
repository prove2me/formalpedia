-- Prove2me | Theorems.Thm_AtomicDynFlow_IDNE_lemma_EC_2
-- name    : AtomicDynFlow.IDNE.lemma_EC_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:16:59.141047+00:00
-- url     : https://prove2.me/theorems/e5be63b5-5f98-4576-bbc4-136bfbe99a64
-- title:
--   Lemma EC.2, p. ec6 (PDF 38) — agents in [k] keep their arrival times and are never overtaken
-- statement:
--   Let agents $1,\dots,k-1$ with paths $P_1,\dots,P_{k-1}$ form a special prefix, and let $(k,P_k)$ be the pair selected next. Write $p_{[k-1]}$ and $p_{[k]}$ for the partial profiles of these agents, and $\ell^v_k[\![k-1]\!]$ for the ideal arrival time of agent $k$ at $v$ given $p_{[k-1]}$. Let $S$ be a set of agents disjoint from $[k-1]$, $j\in S$, $v$ a vertex of $P_k$ (his starting vertex included), and $q$ any path profile. Then
--   $$t^v_k\bigl(p_{[k]},q_{S\setminus\{k\}}\bigr)=\ell^v_k[\![k-1]\!]\le t^v_j\bigl(p_{[k-1]},q_S\bigr),$$
--   where $q_S$ keeps only the agents of $S$, on their $q$-paths, and removes all others.
--
--   The equality says that the arrival times of agent $k$ along his path are unaffected by whichever later agents are present and whatever paths they take; the inequality says that no agent outside $[k-1]$ can reach a vertex of $P_k$ before $k$ does. This lemma is the core of the proof of Theorem 1.
--
--   **Formalization Note.** The paper proves the lemma in the transformed game $\bar\Gamma^N$ of EC.1 (pendant paths carrying the inflows as initial queues) and transfers it to $\Gamma^N$ by Lemma EC.1; here it is stated directly in $\Gamma^N$, with the origin-entrant rule (R3) playing the role of the pendant edges' top priority (T2). Absent agents are removed from the network (`none`), not frozen.
-- source:
--   Cao, Chen, Chen, Wang, Atomic dynamic flow games: adaptive versus nonadaptive agents, accepted manuscript (Operations Research, Oct. 2020; WRAP 143835), p. ec6 (PDF 38), Lemma EC.2, eq. (EC.2); ℓ defined p. ec4 (PDF 36)

import Mathlib
import Definitions.Def_AtomicDynFlow_IDNE_Model
import Definitions.Def_AtomicDynFlow_IDNE_Selection

namespace AtomicDynFlow.IDNE
theorem lemma_EC_2 {V E A : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    [DecidableEq A] (G : Instance V E A) (L : List (A × List E)) (hL : G.IsSpecialPrefix L)
    (k : A) (Pk : List E) (hk : G.IsSelected (prefixProfile L) k Pk)
    (S : Set A) (hS : ∀ b ∈ S, b ∉ L.map Prod.fst) (j : A) (hj : j ∈ S)
    (v : V) (hv : G.OnPath k Pk v) (q : A → List E) (hq : ∀ b, G.IsStrategy b (q b)) :
    G.arrival (overlay (prefixProfile (L ++ [(k, Pk)])) (restrictTo q (S \ {k}))) k v =
        G.ideal (prefixProfile L) k v ∧
      G.ideal (prefixProfile L) k v ≤
        G.arrival (overlay (prefixProfile L) (restrictTo q S)) j v := by sorry
end AtomicDynFlow.IDNE
