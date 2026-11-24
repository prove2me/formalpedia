-- Prove2me | Theorems.Thm_Formalism_L2_DIV_include_right_injective_of_field
-- name    : Formalism.L2.DIV.include_right_injective_of_field
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T13:26:17.9948+00:00
-- url     : https://prove2.me/theorems/d469103e-33f8-42b8-9c6f-99bb69406b23
-- title:
--   DIV: include right injective of field
-- statement:
--   The DIV construction uses the include right injective of field property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/DivisibilityProofs/TuplesP.lean#L64-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/DivisibilityProofs/TuplesP.lean#L64-L66

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

theorem Formalism.L2.DIV.include_right_injective_of_field (R : Type) [CommRing R] [Algebra F R] :
    Function.Injective (Algebra.TensorProduct.includeRight : R →ₐ[F] E ⊗[F] R) := by sorry
