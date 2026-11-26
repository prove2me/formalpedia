-- Prove2me | Theorems.Thm_FD1D_expectedNodePotentialChange_eq
-- name    : FD1D.expectedNodePotentialChange_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:56:23.319165+00:00
-- url     : https://prove2.me/theorems/ba637f1f-838e-4deb-a1bc-9b13fc562e18
-- title:
--   FD1 D: expected Node Potential Change eq
-- statement:
--   The FD1 D construction uses the expected Node Potential Change eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Potential.lean#L44-L56
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Potential.lean#L44-L56

import Definitions.Def_FD1D_Tree
import Definitions.Def_FD1D_Drift
import Definitions.Def_FD1D_Potential
set_option autoImplicit true
open FD1D
noncomputable section
open scoped BigOperators

theorem FD1D.expectedNodePotentialChange_eq
    {a p q : ℝ} {N : ℕ}
    (hzero : N = 0 → q = 0) :
    expectedNodePotentialChange a N p q =
      p * (1 - q) / (N + a + 1) -
        q * (1 - p) / (N + a) := by sorry
