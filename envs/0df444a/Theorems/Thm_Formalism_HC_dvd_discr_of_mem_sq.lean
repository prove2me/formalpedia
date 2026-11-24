-- Prove2me | Theorems.Thm_Formalism_HC_dvd_discr_of_mem_sq
-- name    : Formalism.HC.dvd_discr_of_mem_sq
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T18:31:38.468886+00:00
-- url     : https://prove2.me/theorems/52291aed-7571-4794-bdc7-791cbda510b1
-- title:
--   HC: dvd discr of mem sq
-- statement:
--   The HC construction uses the dvd discr of mem sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/PrimeDiscriminants/RamDiscr.lean#L11-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/PrimeDiscriminants/RamDiscr.lean#L11-L33

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

theorem Formalism.HC.dvd_discr_of_mem_sq (E : Type) [Field E] [NumberField E] {p : ℕ} (hp : p.Prime)
    (h : ∀ P : Ideal (𝓞 E), P.IsPrime → (p : 𝓞 E) ∈ P → (p : 𝓞 E) ∈ P ^ 2) : (p : ℤ) ∣ discr E := by sorry
