-- Prove2me | Theorems.Thm_BlockCycleRotation_invquant
-- name    : BlockCycleRotation.invquant
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-05T09:55:42.870486+00:00
-- url     : https://prove2.me/theorems/6a11a83e-2df7-499a-83d0-054c40894658
-- title:
--   Equation (invquant)
-- statement:
--   The identity of the paper's equation (invquant), relating the quantity counted over quadruples to the divisor-indexed sums used in §4. It is one of the two bookkeeping identities — the other being the Möbius inversion — that let the analysis pass between the sum over all quadruples and the sum over the coprime ones.
-- source:
--   Valentin Blomer and Kai-Uwe Bux, "The cost of cyclic permutations and remainder sums in the Euclidean algorithm", AofA 2026, LIPIcs vol. 381, pp. 14:1-14:17, doi:10.4230/LIPIcs.AofA.2026.14. Numbering follows the full version, arXiv:2601.00979v1 -- Eq. (invquant). Lean source: https://github.com/dbenbenn/block-cycle-rotation/blob/f69003fd8b00c9b5d6d1a4f6807b4943bce0a92c/BlockCycleRotation/TripleSum.lean#L75-L96

import Definitions.Def_BlockCycleRotation_Continuant
import Definitions.Def_BlockCycleRotation_Euclid
import Mathlib

open BlockCycleRotation
open Real Finset

theorem BlockCycleRotation.invquant {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 0 < n →
      ((∑ k ∈ allShifts n, remSum n k : ℕ) : ℝ)
          - ((∑ q ∈ quadruplesAll n, q.2.1 : ℕ) : ℝ)
        ≤ C * (n : ℝ) ^ (1 + ε) := by sorry
