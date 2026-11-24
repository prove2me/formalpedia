-- Prove2me | Theorems.Thm_Formalism_L2_DIV_add_conjugation_mem_range
-- name    : Formalism.L2.DIV.add_conjugation_mem_range
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T13:22:51.158809+00:00
-- url     : https://prove2.me/theorems/7f43c5c6-7770-46f3-8fcb-85db773a95ac
-- title:
--   DIV: add conjugation mem range
-- statement:
--   The DIV construction uses the add conjugation mem range property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/DivisibilityProofs/TuplesP.lean#L42-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/DivisibilityProofs/TuplesP.lean#L42-L53

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_TuplesLemmas
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Afsplit
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsGlob
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsSpan
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_DivisibilityProofs_TuplesP
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain TensorProduct Formalism.UG Formalism.DivisionValues Formalism.EigenvalueLevelCeiling Formalism.UG.P
open scoped nonZeroDivisors
open Formalism Formalism.L2 Formalism.L2.DIV
variable {F E : Type} [Field F] [Field E] [Algebra F E]

theorem Formalism.L2.DIV.add_conjugation_mem_range (σ : E →ₐ[F] E) (hσ : IsConjOf σ) (R : Type) [CommRing R] [Algebra F R] (z : E ⊗[F] R) :
    z + sigR σ R z ∈ (Algebra.TensorProduct.includeRight : R →ₐ[F] E ⊗[F] R).range := by sorry
