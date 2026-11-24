-- Prove2me | Theorems.Thm_Formalism_BasicNotions_Host_q_dvd_discr
-- name    : Formalism.BasicNotions.Host.q_dvd_discr
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T18:31:48.474806+00:00
-- url     : https://prove2.me/theorems/fc2770ee-b069-4661-85ce-d1f111f26b60
-- title:
--   Host: q dvd discr
-- statement:
--   The Host construction uses the q dvd discr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/PrimeDiscriminants/RamDiscr.lean#L56-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/PrimeDiscriminants/RamDiscr.lean#L56-L56

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
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Host
variable {R : Ranks} (H : Host R)

theorem Formalism.BasicNotions.Host.q_dvd_discr : (H.q : ℤ) ∣ discr H.E := by sorry
