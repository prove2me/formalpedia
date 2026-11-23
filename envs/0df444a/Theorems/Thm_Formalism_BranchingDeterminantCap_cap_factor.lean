-- Prove2me | Theorems.Thm_Formalism_BranchingDeterminantCap_cap_factor
-- name    : Formalism.BranchingDeterminantCap.cap_factor
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:26:00.320319+00:00
-- url     : https://prove2.me/theorems/26da1c5a-a126-4115-b86a-70ebb7ddac2a
-- title:
--   Branching Determinant Cap: cap factor
-- statement:
--   The Branching Determinant Cap construction uses the cap factor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/Numeric.lean#L184-L216
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/Numeric.lean#L184-L216

import Definitions.Def_Formalism_BranchSandwichDivisors_NormLog
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_Interlace
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_Numeric
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open Formalism Formalism.BranchingDeterminantCap

theorem Formalism.BranchingDeterminantCap.cap_factor {n : ℕ} {lam : Fin (n + 1) → ℤ} {sg : Fin n → ℤ} (h : Interlace lam sg)
    (i j : Fin n) (v : ℤ) (hv : v ∈ (rset lam sg i).erase (sg i)) :
    ((v - (i : ℤ)) - (sg j - (j : ℤ))) ≠ 0 ∧
    |((v - (i : ℤ)) - (sg j - (j : ℤ)))| ≤ lam 0 - lam (Fin.last n) + (n : ℤ) - 1 := by sorry
