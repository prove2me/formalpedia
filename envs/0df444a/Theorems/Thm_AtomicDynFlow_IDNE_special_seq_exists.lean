-- Prove2me | Theorems.Thm_AtomicDynFlow_IDNE_special_seq_exists
-- name    : AtomicDynFlow.IDNE.special_seq_exists
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T01:17:01.693359+00:00
-- url     : https://prove2.me/theorems/a49f0c21-e34d-440d-a0a7-154f2b29a94b
-- title:
--   EC.2 Algorithm, p. ec3 (PDF 35) — the selection reindexes every agent as 1, 2, …
-- statement:
--   For every instance of $\Gamma^N$ the selection procedure can be iterated to reindex **all** agents of $\Delta$ as $1,2,\dots$ with associated paths $p=(P_1,P_2,\dots)$ such that each agent $k$, with path $P_k$, is the pair selected given $p_{[k-1]}$:
--   $$\exists\,\sigma,\ p:\quad (\sigma,p)\ \text{is a special sequence}.$$
--
--   For finitely many agents this is Algorithm 2 run until every agent is indexed. When $\Delta$ is infinite the content is that no agent is postponed forever: every agent receives a finite index.
--
--   **Formalization Note.** $\sigma:\Delta\to\mathbb N$ is injective with range an initial segment of $\mathbb N$ (all of $\mathbb N$ when $\Delta$ is infinite); agent $a$ has index $\sigma(a)+1$.
-- source:
--   Cao, Chen, Chen, Wang, Atomic dynamic flow games: adaptive versus nonadaptive agents, accepted manuscript (Operations Research, Oct. 2020; WRAP 143835), p. ec3 (PDF 35), EC.2 'Algorithm.' paragraph; p. ec5 (PDF 37), Algorithm 2

import Mathlib
import Definitions.Def_AtomicDynFlow_IDNE_Model
import Definitions.Def_AtomicDynFlow_IDNE_Selection

namespace AtomicDynFlow.IDNE
theorem special_seq_exists {V E A : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    [DecidableEq A] (G : Instance V E A) :
    ∃ (σ : A → ℕ) (p : A → List E), G.IsSpecialSeq σ p := by sorry
end AtomicDynFlow.IDNE
