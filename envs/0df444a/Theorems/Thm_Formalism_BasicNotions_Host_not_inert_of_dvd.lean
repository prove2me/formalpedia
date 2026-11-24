-- Prove2me | Theorems.Thm_Formalism_BasicNotions_Host_not_inert_of_dvd
-- name    : Formalism.BasicNotions.Host.not_inert_of_dvd
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T18:31:32.786542+00:00
-- url     : https://prove2.me/theorems/a8f1328a-db6e-4d7c-8cb1-13d3ec6c8bc0
-- title:
--   Host: not inert of dvd
-- statement:
--   The Host construction uses the not inert of dvd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/DvdCondNIffCls.lean#L22-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/DvdCondNIffCls.lean#L22-L24

import Definitions.Def_Formalism_LocalRingCardinality_DataHost
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_HostFacts
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_DvdCondNIffCls
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Host
variable {R : Ranks} (H : Host R)

theorem Formalism.BasicNotions.Host.not_inert_of_dvd {p : ℕ} (hp : p.Prime) (h : p ∣ H.condN) :
    ¬ (H.cls p = .inertClass ∨ H.cls p = .signal) := by sorry
