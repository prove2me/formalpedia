-- Prove2me | Theorems.Thm_Formalism_BasicNotions_Host_dvd_condN_iff_cls
-- name    : Formalism.BasicNotions.Host.dvd_condN_iff_cls
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T18:31:07.225212+00:00
-- url     : https://prove2.me/theorems/d981ce37-3cb5-42aa-8a75-73ff1c59db5c
-- title:
--   Host: dvd cond N iff cls
-- statement:
--   The Host construction uses the dvd cond N iff cls property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/DvdCondNIffCls.lean#L8-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/DvdCondNIffCls.lean#L8-L20

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

theorem Formalism.BasicNotions.Host.dvd_condN_iff_cls {p : ℕ} (hp : p.Prime) :
    p ∣ H.condN ↔ H.cls p = .ram2 ∨ H.cls p = .ramQ ∨ H.cls p = .ramD := by sorry
