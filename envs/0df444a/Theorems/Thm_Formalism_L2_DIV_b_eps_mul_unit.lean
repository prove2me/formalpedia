-- Prove2me | Theorems.Thm_Formalism_L2_DIV_b_eps_mul_unit
-- name    : Formalism.L2.DIV.b_eps_mul_unit
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T13:23:38.208179+00:00
-- url     : https://prove2.me/theorems/4af60218-ee63-423c-8974-7a84ed344dc9
-- title:
--   DIV: b eps mul unit
-- statement:
--   The DIV construction uses the b eps mul unit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/DivisibilityProofs/TuplesP.lean#L681-L690
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/DivisibilityProofs/TuplesP.lean#L681-L690

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

theorem Formalism.L2.DIV.b_eps_mul_unit (v : HeightOneSpectrum (𝓞 F)) (u : (RInt F E)ˣ)
    (hu : Units.map (RInt F E).subtype.toMonoidHom u ∈ suppAt E v) :
    bEps E v * ((u : RInt F E) - 1) = (u : RInt F E) - 1 := by sorry
