-- Prove2me | Theorems.Thm_Formalism_L2_Host_ne_two_and_ne_q_and_ne_d_of_not_dvd_condN
-- name    : Formalism.L2.Host.ne_two_and_ne_q_and_ne_d_of_not_dvd_condN
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T11:45:49.852795+00:00
-- url     : https://prove2.me/theorems/3739a7b6-03a6-4e18-a2c9-ebda5b234a3d
-- title:
--   Host: ne two and ne q and ne d of not dvd cond N
-- statement:
--   The Host construction uses the ne two and ne q and ne d of not dvd cond N property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/UnitaryNorms/RamificationIdxEqOneOfNotDvd.lean#L16-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/UnitaryNorms/RamificationIdxEqOneOfNotDvd.lean#L16-L23

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

theorem Formalism.L2.Host.ne_two_and_ne_q_and_ne_d_of_not_dvd_condN (p : ℕ) (hnd : ¬ p ∣ H.condN) : p ≠ 2 ∧ p ≠ H.q ∧ p ≠ H.d := by sorry
