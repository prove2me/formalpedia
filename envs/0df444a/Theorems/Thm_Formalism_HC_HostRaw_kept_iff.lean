-- Prove2me | Theorems.Thm_Formalism_HC_HostRaw_kept_iff
-- name    : Formalism.HC.HostRaw.kept_iff
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T02:53:51.481445+00:00
-- url     : https://prove2.me/theorems/f59687b1-a84c-4769-aed7-f935b32add5d
-- title:
--   Host Raw: kept iff
-- statement:
--   The Host Raw construction uses the kept iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/Analytic.lean#L129-L134
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/Analytic.lean#L129-L134

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_PrimePairSizeCondition
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_Analytic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.HC
open Formalism.HC.HostRaw
variable {φ : Frame} (H : HostRaw φ)

theorem Formalism.HC.HostRaw.kept_iff (S : Finset PChar) (θ : φ.Char) : H.Kept S θ ↔ H.prim θ ∈ S := by sorry
