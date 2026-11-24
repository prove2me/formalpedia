-- Prove2me | Theorems.Thm_DetANN_Thm11_outer_small
-- name    : DetANN.Thm11.outer_small
-- status  : Proved
-- author  : @milia
-- created : 2026-11-23T21:58:26.422892+00:00
-- url     : https://prove2.me/theorems/71f08a11-0758-4489-a6e1-e28d2e6be184
-- title:
--   Theorem 1.1, outer programs: the case of a single point
-- statement:
--   For every instance with one point, $P:[1]\to\mathbb R^d$, every $\varepsilon$, and all parameters, the outer preprocessing (definition `DetANN_Thm11_OuterProg`) halts after some $t\le8$ steps with work $t$, without storing to any cell. Moreover, for every query $q\in\mathbb R^d$, the outer query on the stored state halts after some $t'\le5$ steps with work $t'$ and answer pointer $0$, the index of the only point.
--
--   This is the degenerate case $n=1$ of the machine part of Theorem 1.1 (theorem `outer_composition`); the main theorems on preprocessing and queries assume $n\ge2$.
-- source:
--   Original, written for the mission 'Deterministic Approximate Nearest Neighbors in High Dimensions' for the machine part of DetANN.theorem_1_1 (Feng, Indyk, STOC 2027 submission, Theorem 1.1, p.2; the construction of §7.4, p.19). The machine is PNormReg (definition PNormReg_Machine) with the conventions of DetANN_DataStructure.

import Mathlib
import Definitions.Def_PNormReg_Machine
import Definitions.Def_PNormRegLib_Reloc
import Definitions.Def_PNormRegLib_AddressBound
import Definitions.Def_DetANN_DataStructure
import Definitions.Def_DetANN_Construction
import Definitions.Def_DetANN_TupleFamily
import Definitions.Def_DetANN_Thm11_Split
import Definitions.Def_DetANN_Thm11_OuterProg
import Definitions.Def_DetANN_Thm11_Stored

namespace DetANN

namespace Thm11

open PNormReg PNormRegLib

/-- **The case of one point.** With `n = 1` the outer preprocessing halts within 8 steps without
storing to any cell, and every query is answered with index `0` within 5 steps. -/
theorem outer_small :
    ∀ (Pre₃ Qry₃ : Program) (n3 c0 Cb K Cp X3 d : ℕ) (P : Fin 1 → EuclideanSpace ℝ (Fin d)) (ε : ℝ),
      ∃ t : ℕ, t ≤ 8 ∧
        (run (outerPre Pre₃ n3 c0 Cb K Cp X3) (inputState P ε) detTape t).halted = true ∧
        (run (outerPre Pre₃ n3 c0 Cb K Cp X3) (inputState P ε) detTape t).work = t ∧
        cellsWritten (outerPre Pre₃ n3 c0 Cb K Cp X3) (inputState P ε) t = ∅ ∧
        ∀ q : EuclideanSpace ℝ (Fin d), ∃ t' : ℕ, t' ≤ 5 ∧
          (run (outerQry Qry₃ n3 c0 Cb K Cp X3)
            (queryState d (run (outerPre Pre₃ n3 c0 Cb K Cp X3) (inputState P ε) detTape t) q)
            detTape t').halted = true ∧
          (run (outerQry Qry₃ n3 c0 Cb K Cp X3)
            (queryState d (run (outerPre Pre₃ n3 c0 Cb K Cp X3) (inputState P ε) detTape t) q)
            detTape t').work = t' ∧
          (run (outerQry Qry₃ n3 c0 Cb K Cp X3)
            (queryState d (run (outerPre Pre₃ n3 c0 Cb K Cp X3) (inputState P ε) detTape t) q)
            detTape t').core.ptrs 0 = 0 := by
  sorry

end Thm11

end DetANN
