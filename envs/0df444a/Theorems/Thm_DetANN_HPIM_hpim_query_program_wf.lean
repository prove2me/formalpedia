-- Prove2me | Theorems.Thm_DetANN_HPIM_hpim_query_program_wf
-- name    : DetANN.HPIM.hpim_query_program_wf
-- status  : Proved
-- author  : @milia
-- created : 2026-11-16T19:19:35.257567+00:00
-- url     : https://prove2.me/theorems/15fb167f-a3a3-47a2-a470-ae4ff0e0f2b6
-- title:
--   The query program for well-formed HPIM trees
-- statement:
--   There are a deterministic PNormReg program $Q$ and a constant $c_0$ such that the following holds. Let $m\ge1$, and let $T$ be a well-formed HPIM tree (definition `DetANN_HPIMWF`). Let $s$ be a state with $I[1]=m$ that stores $T$ from $I[2]$ (definition `DetANN_HPIMLayout`). On the query state for $q\in\mathbb R^m$ (definition `DetANN_DataStructure`), $Q$ halts with the search result of $T$ at $q$ in pointer register $0$, after work at most
--   $$c_0\,(m+1)\,\mathrm{cost}_T(q).$$
--
--   This corrects `DetANN.HPIM.hpim_query_program`, which omits well-formedness and is false: the layout does not store the number $n$ of local points, so one memory can store two trees that differ only in $n$ and that have different search results.
-- source:
--   Original, written for the mission 'Deterministic Approximate Nearest Neighbors in High Dimensions' as part of a floor-free proof of DetANN.lemma_3_3 (Feng, Indyk, STOC 2027 submission, Lemma 3.3, p.7). It corrects DetANN.HPIM.hpim_query_program, which is false because the layout does not store the number of local points.

import Mathlib
import Definitions.Def_PNormReg_Machine
import Definitions.Def_DetANN_DataStructure
import Definitions.Def_DetANN_HPIMLayout
import Definitions.Def_DetANN_HPIMWF

namespace DetANN.HPIM

/-- **The query program** (for well-formed trees). One deterministic PNormReg program reads any
well-formed HPIM tree stored from `I[2]` (with `I[1] = m`) in the layout of `DetANN_HPIMLayout`. On the
query `q` it halts with the search result in pointer register `0`, after work at most `c₀ (m + 1)`
times the cost of the search. -/
theorem hpim_query_program_wf :
    ∃ Qry : PNormReg.Program, DetProgram Qry ∧ ∃ c₀ : ℕ,
      ∀ (m : ℕ) (s : PNormReg.State) (T : HTree m) (q : EuclideanSpace ℝ (Fin m)),
        1 ≤ m → T.WF → s.integerMemory 1 = m → HTreeAt m s (s.integerMemory 2) T →
        ∃ t : ℕ,
          (PNormReg.run Qry (queryState m s q) detTape t).halted = true ∧
          (PNormReg.run Qry (queryState m s q) detTape t).work ≤ c₀ * (m + 1) * T.cost q ∧
          (PNormReg.run Qry (queryState m s q) detTape t).core.ptrs 0 = T.search q := by sorry

end DetANN.HPIM
