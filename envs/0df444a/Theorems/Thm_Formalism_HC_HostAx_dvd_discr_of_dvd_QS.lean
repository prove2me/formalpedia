-- Prove2me | Theorems.Thm_Formalism_HC_HostAx_dvd_discr_of_dvd_QS
-- name    : Formalism.HC.HostAx.dvd_discr_of_dvd_QS
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T18:31:00.576857+00:00
-- url     : https://prove2.me/theorems/1e6f4a88-465f-4f83-863b-59e3190fdc7d
-- title:
--   Host Ax: dvd discr of dvd QS
-- statement:
--   The Host Ax construction uses the dvd discr of dvd QS property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/PrimeDiscriminants/RamDiscr.lean#L46-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/PrimeDiscriminants/RamDiscr.lean#L46-L48

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataHost
import Definitions.Def_Development_AutomorphicArithmetic_PrimeDiscriminants_SmallRam
import Definitions.Def_Development_AutomorphicArithmetic_PrimeDiscriminants_RamDiscr
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Ideal
noncomputable section
open Formalism Formalism.HC

theorem Formalism.HC.HostAx.dvd_discr_of_dvd_QS {φ : Frame} (H : HostAx φ) (hE : H.toHostRaw.Exact) {l : ℕ} (hl : l.Prime) (hd : l ∣ H.QS) :
    (l : ℤ) ∣ discr H.E := by sorry
