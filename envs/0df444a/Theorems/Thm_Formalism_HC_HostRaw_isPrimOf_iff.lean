-- Prove2me | Theorems.Thm_Formalism_HC_HostRaw_isPrimOf_iff
-- name    : Formalism.HC.HostRaw.isPrimOf_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:14:23.443216+00:00
-- url     : https://prove2.me/theorems/a2752329-26e2-40ef-82d1-5aaa20dc0075
-- title:
--   Host Raw: is Prim Of iff
-- statement:
--   The Host Raw construction uses the is Prim Of iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/Analytic.lean#L113-L119
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/Analytic.lean#L113-L119

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

theorem Formalism.HC.HostRaw.isPrimOf_iff (θ : φ.Char) (ψ : PChar) : H.IsPrimOf θ ψ.χ ↔ ψ = H.prim θ := by sorry
