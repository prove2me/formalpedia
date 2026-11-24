-- Prove2me | Theorems.Thm_Formalism_BasicNotions_Host_dvd_natAbs_discr_iff
-- name    : Formalism.BasicNotions.Host.dvd_natAbs_discr_iff
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T18:31:19.92003+00:00
-- url     : https://prove2.me/theorems/f4e4748b-f0e1-4a40-962e-7d8604efc0b5
-- title:
--   Host: dvd nat Abs discr iff
-- statement:
--   The Host construction uses the dvd nat Abs discr iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/PrimeDiscriminants/RamDiscr.lean#L65-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/PrimeDiscriminants/RamDiscr.lean#L65-L66

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

theorem Formalism.BasicNotions.Host.dvd_natAbs_discr_iff {p : ℕ} (hp : p.Prime) : p ∣ (discr H.E).natAbs ↔ p ∣ H.condN := by sorry
