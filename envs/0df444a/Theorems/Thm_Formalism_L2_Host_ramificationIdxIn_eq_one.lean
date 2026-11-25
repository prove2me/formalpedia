-- Prove2me | Theorems.Thm_Formalism_L2_Host_ramificationIdxIn_eq_one
-- name    : Formalism.L2.Host.ramificationIdxIn_eq_one
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T11:45:35.789606+00:00
-- url     : https://prove2.me/theorems/5a5d996e-533f-5714-a271-b2656797c71c
-- title:
--   Host: ramification Idx In eq one
-- statement:
--   The Host construction uses the ramification Idx In eq one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/UnitaryNorms/RamificationIdxEqOneOfNotDvd.lean#L33-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/UnitaryNorms/RamificationIdxEqOneOfNotDvd.lean#L33-L49

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataHost
import Definitions.Def_Formalism_FrobeniusOrbits_HostCorollaries
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_HostFacts
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_RamificationIdxEqOneOfNotDvd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Ideal
open Formalism Formalism.L2 Formalism.L2.Host
open Formalism.BasicNotions Formalism.FrobeniusOrbits
variable {R : Ranks} (H : Formalism.BasicNotions.Host R)

theorem Formalism.L2.Host.ramificationIdxIn_eq_one (p : ℕ) [Fact p.Prime] (hnd : ¬ p ∣ H.condN) :
    (span {(p : ℤ)}).ramificationIdxIn (𝓞 H.E) = 1 := by sorry
