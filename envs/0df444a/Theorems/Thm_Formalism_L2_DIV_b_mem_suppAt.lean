-- Prove2me | Theorems.Thm_Formalism_L2_DIV_b_mem_suppAt
-- name    : Formalism.L2.DIV.b_mem_suppAt
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T13:22:39.469044+00:00
-- url     : https://prove2.me/theorems/81b95fb7-1006-498b-834d-e82639637b6a
-- title:
--   DIV: b mem supp At
-- statement:
--   The DIV construction uses the b mem supp At property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/DivisibilityProofs/TuplesP.lean#L666-L669
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/DivisibilityProofs/TuplesP.lean#L666-L669

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

theorem Formalism.L2.DIV.b_mem_suppAt (v : HeightOneSpectrum (𝓞 F)) (x : (AfE F E)ˣ) :
    x ∈ suppAt E v ↔ ∀ v' : HeightOneSpectrum (𝓞 F), v' ≠ v → prV (E := E) v' (x : AfE F E) = 1 := by sorry
