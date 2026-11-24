-- Prove2me | Theorems.Thm_Formalism_HC_dvd_discr_of_sqrt
-- name    : Formalism.HC.dvd_discr_of_sqrt
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T18:30:39.546632+00:00
-- url     : https://prove2.me/theorems/7e854614-3613-4e00-af5d-c1ae2eaa23dd
-- title:
--   HC: dvd discr of sqrt
-- statement:
--   The HC construction uses the dvd discr of sqrt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/PrimeDiscriminants/RamDiscr.lean#L35-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/PrimeDiscriminants/RamDiscr.lean#L35-L44

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

theorem Formalism.HC.dvd_discr_of_sqrt (E : Type) [Field E] [NumberField E] {p : ℕ} (hp : p.Prime) {a : E} (ha : a ^ 2 = -(p : E)) :
    (p : ℤ) ∣ discr E := by sorry
