-- Prove2me | Theorems.Thm_Formalism_BranchingDeterminantCap_interlace_antitone
-- name    : Formalism.BranchingDeterminantCap.interlace_antitone
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:24:08.895449+00:00
-- url     : https://prove2.me/theorems/56a70a5b-fd31-4ba3-a81b-fb46c372b2f0
-- title:
--   Branching Determinant Cap: interlace antitone
-- statement:
--   The Branching Determinant Cap construction uses the interlace antitone property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/Numeric.lean#L181-L182
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/Numeric.lean#L181-L182

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

theorem Formalism.BranchingDeterminantCap.interlace_antitone {n : ℕ} {lam : Fin (n + 1) → ℤ} {sg : Fin n → ℤ}
    (h : Interlace lam sg) : Antitone lam := by sorry
