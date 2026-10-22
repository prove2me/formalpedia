-- Prove2me | Theorems.Thm_AtomicDynFlow_IDNE_theorem_EC_2
-- name    : AtomicDynFlow.IDNE.theorem_EC_2
-- status  : Disproved
-- author  : @mikedeng1
-- created : 2026-10-19T01:17:12.307296+00:00
-- url     : https://prove2.me/theorems/ec8ce16b-ecb4-4ecc-96cf-caf87869496c
-- title:
--   Theorem EC.2, p. ec8 (PDF 40); §4.1, p. 14 — the special sequence is an IDNE
-- statement:
--   Let the agents be reindexed as $1,2,\dots$ with paths $p=(P_k)_{k\in\Delta}$ forming a special sequence: each $(k,P_k)$ is the pair selected by (S1)–(S3) given $p_{[k-1]}$. Then $p$ is an iteratively dominant NE with this order: for every $k$, every vertex $v$ of $P_k$ and every path profile $q$ of the agents outside $[k]$,
--   $$t^v_k(p_{[k]},q)=\min\bigl\{t^v_j(p_{[k-1]},r): j\in\Delta\setminus[k-1],\ r \text{ a path profile of } \Delta\setminus[k-1]\bigr\}.$$
--
--   The paper calls such a profile a *special IDNE*. With the existence of a special sequence it yields Theorem 1.
--
--   **Formalization Note.** Stated in $\Gamma^N$; the paper proves it in the transformed game $\bar\Gamma^N$ and transfers it by Lemma EC.1. The conclusion uses the same reindexing $\sigma$ as the hypothesis.
-- source:
--   Cao, Chen, Chen, Wang, Atomic dynamic flow games: adaptive versus nonadaptive agents, accepted manuscript (Operations Research, Oct. 2020; WRAP 143835), p. ec8 (PDF 40), Theorem EC.2; p. 14 (PDF 15), §4.1 'It turns out that the path profile … is indeed an IDNE'

import Mathlib
import Definitions.Def_AtomicDynFlow_IDNE_Model
import Definitions.Def_AtomicDynFlow_IDNE_Equilibrium
import Definitions.Def_AtomicDynFlow_IDNE_Selection

namespace AtomicDynFlow.IDNE
theorem theorem_EC_2 {V E A : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    [DecidableEq A] (G : Instance V E A) (σ : A → ℕ) (p : A → List E)
    (h : G.IsSpecialSeq σ p) : G.IsIDNEWith σ p := by sorry
end AtomicDynFlow.IDNE
