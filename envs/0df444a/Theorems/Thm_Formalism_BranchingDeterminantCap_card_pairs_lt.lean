-- Prove2me | Theorems.Thm_Formalism_BranchingDeterminantCap_card_pairs_lt
-- name    : Formalism.BranchingDeterminantCap.card_pairs_lt
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T10:26:10.753031+00:00
-- url     : https://prove2.me/theorems/b4bf1c10-7748-4ae0-ac28-b903137df9f2
-- title:
--   Branching Determinant Cap: card pairs lt
-- statement:
--   The Branching Determinant Cap construction uses the card pairs lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/Numeric.lean#L314-L327
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/Numeric.lean#L314-L327

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

theorem Formalism.BranchingDeterminantCap.card_pairs_lt (n : ℕ) :
    ((Finset.univ : Finset (Fin (n + 1) × Fin (n + 1))).filter (fun p => p.1 < p.2)).card =
      (n + 1) * n / 2 := by sorry
