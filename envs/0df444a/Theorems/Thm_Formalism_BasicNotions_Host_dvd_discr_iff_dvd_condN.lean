-- Prove2me | Theorems.Thm_Formalism_BasicNotions_Host_dvd_discr_iff_dvd_condN
-- name    : Formalism.BasicNotions.Host.dvd_discr_iff_dvd_condN
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T18:32:11.263047+00:00
-- url     : https://prove2.me/theorems/a9c8ccba-40a5-40db-903d-c2b7aa587e6d
-- title:
--   Host: dvd discr iff dvd cond N
-- statement:
--   The Host construction uses the dvd discr iff dvd cond N property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/PrimeDiscriminants/RamDiscr.lean#L58-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/PrimeDiscriminants/RamDiscr.lean#L58-L63

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

theorem Formalism.BasicNotions.Host.dvd_discr_iff_dvd_condN {p : ℕ} (hp : p.Prime) : (p : ℤ) ∣ discr H.E ↔ p ∣ H.condN := by sorry
