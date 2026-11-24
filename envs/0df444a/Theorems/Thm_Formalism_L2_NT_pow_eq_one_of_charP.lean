-- Prove2me | Theorems.Thm_Formalism_L2_NT_pow_eq_one_of_charP
-- name    : Formalism.L2.NT.pow_eq_one_of_charP
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T17:55:35.844243+00:00
-- url     : https://prove2.me/theorems/43b01860-ba83-48d3-bf20-958f0eb61296
-- title:
--   NT: pow eq one of char P
-- statement:
--   The NT construction uses the pow eq one of char P property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/NormalizedHeckeFactors/TypesDefs.lean#L128-L132
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/NormalizedHeckeFactors/TypesDefs.lean#L128-L132

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
variable (B : ValuationSubring Ω) {l : ℕ} [Fact l.Prime] (κ : IsLocalRing.ResidueField B ≃+* Formalism.CyclotomicNorms.Fbar l)

theorem Formalism.L2.NT.pow_eq_one_of_charP {k : Type} [Field k] (l : ℕ) [Fact l.Prime] [CharP k l] (y : k) (a m : ℕ)
    (h : y ^ (l ^ a * m) = 1) : y ^ m = 1 := by sorry
