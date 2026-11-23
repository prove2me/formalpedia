-- Prove2me | Theorems.Thm_Formalism_HC_HostRaw_isPrimOf_prim
-- name    : Formalism.HC.HostRaw.isPrimOf_prim
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T02:13:58.76974+00:00
-- url     : https://prove2.me/theorems/1a5ebc0e-bea1-4b13-bff0-ae5297f736c3
-- title:
--   Host Raw: is Prim Of prim
-- statement:
--   The Host Raw construction uses the is Prim Of prim property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/Analytic.lean#L110-L111
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/Analytic.lean#L110-L111

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

theorem Formalism.HC.HostRaw.isPrimOf_prim (θ : φ.Char) : H.IsPrimOf θ (H.prim θ).χ := by sorry
