-- Prove2me | Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_rank_bord_le
-- name    : Formalism.GaloisIrreducibility.BorderedIndexCases.rank_bord_le
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T22:52:35.833494+00:00
-- url     : https://prove2.me/theorems/835a59bc-d2bc-4314-adf3-872aceb2ed7a
-- title:
--   Bordered Index Cases: rank bord le
-- statement:
--   The Bordered Index Cases construction uses the rank bord le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaloisIrreducibility/GaloisIrreducibilityProofs/OneNonUnit.lean#L69-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaloisIrreducibility/GaloisIrreducibilityProofs/OneNonUnit.lean#L69-L86

import Definitions.Def_Formalism_GaloisIrreducibility_Statement
import Definitions.Def_Formalism_GaloisIrreducibility_GaloisIrreducibilityProofs_OneNonUnit
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GaloisIrreducibility
open Matrix
open Formalism.GaloisIrreducibility.BorderedIndexCases
variable {R : Type} [CommRing R]

theorem Formalism.GaloisIrreducibility.BorderedIndexCases.rank_bord_le {K : Type} [Field K] {m : ℕ} (M : Matrix (Fin m) (Fin m) K) :
    (bord M).rank ≤ M.rank + 1 := by sorry
