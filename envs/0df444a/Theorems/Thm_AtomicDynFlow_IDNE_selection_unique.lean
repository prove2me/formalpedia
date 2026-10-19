-- Prove2me | Theorems.Thm_AtomicDynFlow_IDNE_selection_unique
-- name    : AtomicDynFlow.IDNE.selection_unique
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:17:06.805067+00:00
-- url     : https://prove2.me/theorems/9f4c85c3-8805-4930-82f6-9a619a750bda
-- title:
--   §4.1, p. 14 (PDF 15) — the pruning (S1)–(S3) ends in exactly one candidate pair
-- statement:
--   Consider an instance of the game $\Gamma^N$ and suppose that agents $1,\dots,k-1$ and their dominant paths have been identified by the construction of §4.1, i.e. they form a special prefix. If some agent remains unidentified, then the pruning (S1)–(S3), followed by the final tie-break by initial-queue rank or original rank, leaves exactly one candidate pair:
--   $$\exists!\,(j,P_j):\quad (j,P_j)\ \text{is selected given } p_{[k-1]} .$$
--
--   This is the step that makes the construction well defined: it identifies the $k$th agent and his dominant path. The agent set may be infinite, so the candidate set may be infinite.
--
--   **Formalization Note.** "Selected" is `IsSelected`, the pairwise backward comparison of the Selection file. The special prefix is a list of (agent, path) pairs; "some agent remains" means some agent is not listed.
-- source:
--   Cao, Chen, Chen, Wang, Atomic dynamic flow games: adaptive versus nonadaptive agents, accepted manuscript (Operations Research, Oct. 2020; WRAP 143835), p. 14 (PDF 15), §4.1, 'It can be seen that either the above process is terminated …'

import Mathlib
import Definitions.Def_AtomicDynFlow_IDNE_Model
import Definitions.Def_AtomicDynFlow_IDNE_Selection

namespace AtomicDynFlow.IDNE
theorem selection_unique {V E A : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    [DecidableEq A] (G : Instance V E A) (L : List (A × List E)) (hL : G.IsSpecialPrefix L)
    (hrem : ∃ j : A, j ∉ L.map Prod.fst) :
    ∃! jP : A × List E, G.IsSelected (prefixProfile L) jP.1 jP.2 := by sorry
end AtomicDynFlow.IDNE
