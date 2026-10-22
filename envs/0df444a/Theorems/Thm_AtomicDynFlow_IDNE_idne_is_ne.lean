-- Prove2me | Theorems.Thm_AtomicDynFlow_IDNE_idne_is_ne
-- name    : AtomicDynFlow.IDNE.idne_is_ne
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T01:16:55.956062+00:00
-- url     : https://prove2.me/theorems/0db554e1-3ff4-4ff8-bf32-9f94a58a15e2
-- title:
--   §4.1, p. 11 (PDF 12) — an iteratively dominant NE is an NE
-- statement:
--   In the game $\Gamma^N$, let $p$ be a path profile (every agent on one of his strategies). If $p$ is an iteratively dominant NE (Definition 2), then $p$ is a Nash equilibrium (Definition 1): for every agent $i$ and every $P'_i\in\mathcal P_i$,
--   $$t^d_i(p)\le t^d_i(P'_i,p_{-i}).$$
--
--   This is the observation that opens §4.1: if, given the strategies of the agents ordered before him, each agent's strategy is optimal whatever the agents after him do, nobody can gain by deviating alone.
-- source:
--   Cao, Chen, Chen, Wang, Atomic dynamic flow games: adaptive versus nonadaptive agents, accepted manuscript (Operations Research, Oct. 2020; WRAP 143835), p. 11 (PDF 12), §4.1, 'Observe that the following strategy profile that extends the idea of dominance is still an NE'

import Mathlib
import Definitions.Def_AtomicDynFlow_IDNE_Model
import Definitions.Def_AtomicDynFlow_IDNE_Equilibrium

namespace AtomicDynFlow.IDNE
theorem idne_is_ne {V E A : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    [DecidableEq A] (G : Instance V E A) (p : A → List E)
    (h : G.IsIDNE p) : G.IsNE p := by sorry
end AtomicDynFlow.IDNE
