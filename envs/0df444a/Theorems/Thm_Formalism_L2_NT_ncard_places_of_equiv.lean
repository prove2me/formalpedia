-- Prove2me | Theorems.Thm_Formalism_L2_NT_ncard_places_of_equiv
-- name    : Formalism.L2.NT.ncard_places_of_equiv
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T17:55:45.406255+00:00
-- url     : https://prove2.me/theorems/54ef41c9-1991-49cb-b9f7-9d400a8c7431
-- title:
--   NT: ncard places of equiv
-- statement:
--   The NT construction uses the ncard places of equiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/NormalizedHeckeFactors/TypesDefs.lean#L33-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/NormalizedHeckeFactors/TypesDefs.lean#L33-L57

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

theorem Formalism.L2.NT.ncard_places_of_equiv {A B : Type} [Field A] [Field B] (e : A ≃+* B) (p : ℕ) :
    ({v : HeightOneSpectrum (𝓞 A) | ((p : ℕ) : 𝓞 A) ∈ v.asIdeal}).ncard =
      ({v : HeightOneSpectrum (𝓞 B) | ((p : ℕ) : 𝓞 B) ∈ v.asIdeal}).ncard := by sorry
