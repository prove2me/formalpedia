-- Prove2me | Theorems.Thm_Formalism_L2_NT_IsTeich_injective
-- name    : Formalism.L2.NT.IsTeich.injective
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T17:56:27.539243+00:00
-- url     : https://prove2.me/theorems/f96cdfb1-74e9-48e3-ab8c-329f412217c9
-- title:
--   Is Teich: injective
-- statement:
--   The Is Teich construction uses the injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/NormalizedHeckeFactors/TypesDefs.lean#L67-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/NormalizedHeckeFactors/TypesDefs.lean#L67-L75

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

theorem Formalism.L2.NT.IsTeich.injective {Ω : Type} [Field Ω] {A : ValuationSubring Ω} {p : ℕ} [Fact p.Prime]
    {κ : IsLocalRing.ResidueField A ≃+* Formalism.CyclotomicNorms.Fbar p} {t : Formalism.CyclotomicNorms.Fbar p →* Ω} (h : IsTeich A κ t) :
    Function.Injective t := by sorry
