-- Prove2me | Theorems.Thm_Formalism_HC_EvenData_mem_cusp_forms_iff_automorphic_compact
-- name    : Formalism.HC.EvenData.mem_cusp_forms_iff_automorphic_compact
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T20:30:41.66042+00:00
-- url     : https://prove2.me/theorems/6d68612c-9e8b-42c9-8d64-cf34d8e023f7
-- title:
--   Even Data: mem cusp forms iff automorphic compact
-- statement:
--   The Even Data construction uses the mem cusp forms iff automorphic compact property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/InertiaGaloisSymmetry/OfCharFrame.lean#L179-L187
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/InertiaGaloisSymmetry/OfCharFrame.lean#L179-L187

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_OfChar
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ArtinMapSecondEqJacobiSymOfModEq
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_FrameFacts
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_OfCharFrame
import Theorems.Thm_Formalism_HC_Frame_mem_cusp_forms_iff_automorphic_compact

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
open Formalism.FrobeniusOrbits
attribute [instance] EvenData.grp
open Formalism.HC.EvenData
variable (D : EvenData)

theorem Formalism.HC.EvenData.mem_cusp_forms_iff_automorphic_compact (t : D.frame.A) : t ∈ D.frame.A0 ↔ D.xiA (D.frame.iota t) = 1 := by sorry
