-- Prove2me | Theorems.Thm_Formalism_L2_DIV_b_mkU_idF
-- name    : Formalism.L2.DIV.b_mkU_idF
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T13:22:48.563328+00:00
-- url     : https://prove2.me/theorems/38af9f29-ac9b-4950-bc1f-1bb8e846cb07
-- title:
--   DIV: b mk U id F
-- statement:
--   The DIV construction uses the b mk U id F property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/DivisibilityProofs/TuplesP.lean#L1208-L1235
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/DivisibilityProofs/TuplesP.lean#L1208-L1235

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
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {L : Type} [Field L]

theorem Formalism.L2.DIV.b_mkU_idF (v : HeightOneSpectrum (𝓞 F)) (n : 𝓞 F) (hn : n ∉ v.asIdeal) (u : (RInt F E)ˣ)
    (hu : (u : RInt F E) = toRInt F E (algebraMap (𝓞 F) (𝓞 E) n) * bEps E v + (1 - bEps E v)) :
    Units.map (RInt F E).subtype.toMonoidHom u ∈ (idF F E).range := by sorry
