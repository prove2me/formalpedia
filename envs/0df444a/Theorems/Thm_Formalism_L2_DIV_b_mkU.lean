-- Prove2me | Theorems.Thm_Formalism_L2_DIV_b_mkU
-- name    : Formalism.L2.DIV.b_mkU
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T13:22:45.557084+00:00
-- url     : https://prove2.me/theorems/4ac1e35e-ec6e-449a-a298-220a573c3fe0
-- title:
--   DIV: b mk U
-- statement:
--   The DIV construction uses the b mk U property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/DivisibilityProofs/TuplesP.lean#L945-L959
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/DivisibilityProofs/TuplesP.lean#L945-L959

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

theorem Formalism.L2.DIV.b_mkU (v : HeightOneSpectrum (𝓞 F)) (b c : 𝓞 E) (r : 𝓞 F) (hr : r ∉ v.asIdeal)
    (hbc : b * c = algebraMap (𝓞 F) (𝓞 E) r) :
    ∃ u : (RInt F E)ˣ, (u : RInt F E) = toRInt F E b * bEps E v + (1 - bEps E v) := by sorry
