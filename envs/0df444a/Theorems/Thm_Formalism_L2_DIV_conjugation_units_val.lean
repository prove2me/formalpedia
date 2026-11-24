-- Prove2me | Theorems.Thm_Formalism_L2_DIV_conjugation_units_val
-- name    : Formalism.L2.DIV.conjugation_units_val
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T13:22:12.399734+00:00
-- url     : https://prove2.me/theorems/912f44b0-a4ad-4dcb-b8ca-91242a63966d
-- title:
--   DIV: conjugation units val
-- statement:
--   The DIV construction uses the conjugation units val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/DivisibilityProofs/TuplesP.lean#L103-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/DivisibilityProofs/TuplesP.lean#L103-L104

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

theorem Formalism.L2.DIV.conjugation_units_val (σ : E →ₐ[F] E) (x : (AfE F E)ˣ) :
    ((conjId σ x : (AfE F E)ˣ) : AfE F E) = sigR σ (FiniteAdeleRing (𝓞 F) F) (x : AfE F E) := by sorry
