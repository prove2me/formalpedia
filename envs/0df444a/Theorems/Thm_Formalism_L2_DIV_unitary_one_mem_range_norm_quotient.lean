-- Prove2me | Theorems.Thm_Formalism_L2_DIV_unitary_one_mem_range_norm_quotient
-- name    : Formalism.L2.DIV.unitary_one_mem_range_norm_quotient
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T13:25:35.724639+00:00
-- url     : https://prove2.me/theorems/3a015d19-8262-44f6-bb81-72502fdfebf9
-- title:
--   DIV: unitary one mem range norm quotient
-- statement:
--   The DIV construction uses the unitary one mem range norm quotient property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/DivisibilityProofs/TuplesP.lean#L272-L411
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/DivisibilityProofs/TuplesP.lean#L272-L411

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
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
local notation "𝔸" => FiniteAdeleRing (𝓞 F) F

theorem Formalism.L2.DIV.unitary_one_mem_range_norm_quotient (σ : E →ₐ[F] E) (hσ : IsConjOf σ) (y : (AfE F E)ˣ) (hy : y ∈ U1 σ) :
    y ∈ (h90 σ).range := by sorry
