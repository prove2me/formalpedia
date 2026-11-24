-- Prove2me | Theorems.Thm_Formalism_L2_DIV_b_same
-- name    : Formalism.L2.DIV.b_same
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T13:22:04.370993+00:00
-- url     : https://prove2.me/theorems/363bde7d-0751-42be-adac-71470004e84a
-- title:
--   DIV: b same
-- statement:
--   The DIV construction uses the b same property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/DivisibilityProofs/TuplesP.lean#L1056-L1073
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/DivisibilityProofs/TuplesP.lean#L1056-L1073

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
variable {L : Type} [Field L]

theorem Formalism.L2.DIV.b_same (ξ : Chr F E L) (hξ : ∀ v : HeightOneSpectrum (𝓞 F), wildAt E v ≤ ξ.ker)
    (v : HeightOneSpectrum (𝓞 F)) (u u' : (RInt F E)ˣ)
    (hu : Units.map (RInt F E).subtype.toMonoidHom u ∈ suppAt E v)
    (hu' : Units.map (RInt F E).subtype.toMonoidHom u' ∈ suppAt E v)
    (h : ∀ P : HeightOneSpectrum (𝓞 E), (u : RInt F E) - u' ∈ P.asIdeal.map (toRInt F E)) :
    ξ (Units.map (RInt F E).subtype.toMonoidHom u) = ξ (Units.map (RInt F E).subtype.toMonoidHom u') := by sorry
