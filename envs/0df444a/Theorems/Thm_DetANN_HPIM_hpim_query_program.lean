-- Prove2me | Theorems.Thm_DetANN_HPIM_hpim_query_program
-- name    : DetANN.HPIM.hpim_query_program
-- status  : Disproved
-- author  : @milia
-- created : 2026-11-16T06:36:44.817307+00:00
-- url     : https://prove2.me/theorems/914f4703-6193-422d-b254-b82bea90b291
-- title:
--   The query program for HPIM trees
-- statement:
--   There are a deterministic PNormReg program $Q$ and a constant $c_0$ such that the following holds. Let $m\ge1$, let $T$ be any HPIM tree, and let $s$ be a state with $I[1]=m$ that stores $T$ from $I[2]$ (definition `DetANN_HPIMLayout`). On the query state for $q\in\mathbb R^m$ (definition `DetANN_DataStructure`), $Q$ halts with the search result of $T$ at $q$ in pointer register $0$, after work at most
--   $$c_0\,(m+1)\,\mathrm{cost}_T(q).$$
--
--   Each node visit compares $q$ with a box, or reads an index, in $O(m)$ steps. The ladder search reads the table of powers, so no pointer division is needed.
-- source:
--   Original, written for the mission 'Deterministic Approximate Nearest Neighbors in High Dimensions' as part of a floor-free proof of DetANN.lemma_3_3 (Feng, Indyk, STOC 2027 submission, Lemma 3.3, p.7). The search tree follows Har-Peled, Indyk, Motwani, Approximate nearest neighbor: towards removing the curse of dimensionality, Theory of Computing 8 (2012), §2, made deterministic and floor-free. The machine is PNormReg (definition PNormReg_Machine) with the conventions of DetANN_DataStructure.

import Mathlib
import Definitions.Def_PNormReg_Machine
import Definitions.Def_DetANN_DataStructure
import Definitions.Def_DetANN_HPIMLayout

namespace DetANN.HPIM

/-- **The query program.** One deterministic PNormReg program reads any HPIM tree stored from
`I[2]` (with `I[1] = m`) in the layout of `DetANN_HPIMLayout`. On the query `q` it halts with the
search result in pointer register `0`, after work at most `c₀ (m + 1)` times the cost of the search. -/
theorem hpim_query_program :
    ∃ Qry : PNormReg.Program, DetProgram Qry ∧ ∃ c₀ : ℕ,
      ∀ (m : ℕ) (s : PNormReg.State) (T : HTree m) (q : EuclideanSpace ℝ (Fin m)),
        1 ≤ m → s.integerMemory 1 = m → HTreeAt m s (s.integerMemory 2) T →
        ∃ t : ℕ,
          (PNormReg.run Qry (queryState m s q) detTape t).halted = true ∧
          (PNormReg.run Qry (queryState m s q) detTape t).work ≤ c₀ * (m + 1) * T.cost q ∧
          (PNormReg.run Qry (queryState m s q) detTape t).core.ptrs 0 = T.search q := by sorry

end DetANN.HPIM
