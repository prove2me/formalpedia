-- Prove2me | Theorems.Thm_Formalism_L2_DIV_conjugation_fixed_mem_range
-- name    : Formalism.L2.DIV.conjugation_fixed_mem_range
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T13:22:48.670865+00:00
-- url     : https://prove2.me/theorems/e7dcd42f-338e-4025-81df-959d84adcb30
-- title:
--   DIV: conjugation fixed mem range
-- statement:
--   The DIV construction uses the conjugation fixed mem range property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/DivisibilityProofs/TuplesP.lean#L55-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/DivisibilityProofs/TuplesP.lean#L55-L62

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

theorem Formalism.L2.DIV.conjugation_fixed_mem_range [CharZero F] (σ : E →ₐ[F] E) (hσ : IsConjOf σ) (R : Type) [CommRing R] [Algebra F R]
    (z : E ⊗[F] R) (hz : sigR σ R z = z) :
    z ∈ (Algebra.TensorProduct.includeRight : R →ₐ[F] E ⊗[F] R).range := by sorry
