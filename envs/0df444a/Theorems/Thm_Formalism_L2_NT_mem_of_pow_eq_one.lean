-- Prove2me | Theorems.Thm_Formalism_L2_NT_mem_of_pow_eq_one
-- name    : Formalism.L2.NT.mem_of_pow_eq_one
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T17:55:33.241799+00:00
-- url     : https://prove2.me/theorems/e2a06f0d-3390-4e90-8027-86818dc94172
-- title:
--   NT: mem of pow eq one
-- statement:
--   The NT construction uses the mem of pow eq one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/NormalizedHeckeFactors/TypesDefs.lean#L95-L107
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/NormalizedHeckeFactors/TypesDefs.lean#L95-L107

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_RealCyclotomicTwoPower
import Definitions.Def_Formalism_CyclotomicNorms_StatementT
import Definitions.Def_Formalism_LocalToGlobal_NormalizedHeckeFactors_TypesDefs
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Polynomial
open Formalism Formalism.L2 Formalism.L2.NT
open Formalism.L2.Host
variable {Ω : Type} [Field Ω]

theorem Formalism.L2.NT.mem_of_pow_eq_one (B : ValuationSubring Ω) {z : Ω} {n : ℕ} (hn : 0 < n) (h : z ^ n = 1) : z ∈ B := by sorry
