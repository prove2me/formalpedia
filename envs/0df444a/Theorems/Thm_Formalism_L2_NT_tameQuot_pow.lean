-- Prove2me | Theorems.Thm_Formalism_L2_NT_tameQuot_pow
-- name    : Formalism.L2.NT.tameQuot_pow
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T17:54:36.993674+00:00
-- url     : https://prove2.me/theorems/2529e815-4b09-4c4e-9b49-22fe3a00315b
-- title:
--   NT: tame Quot pow
-- statement:
--   The NT construction uses the tame Quot pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/NormalizedHeckeFactors/TypesDefs.lean#L310-L313
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/NormalizedHeckeFactors/TypesDefs.lean#L310-L313

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

theorem Formalism.L2.NT.tameQuot_pow {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω] (σ : Ω ≃ₐ[E] Ω) {y : Ω} {m p : ℕ}
    (hp : (p : Ω) ≠ 0) (hy : y ^ m = (p : Ω)) : (σ y / y) ^ m = 1 := by sorry
