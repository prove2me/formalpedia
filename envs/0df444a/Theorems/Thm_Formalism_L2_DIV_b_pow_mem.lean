-- Prove2me | Theorems.Thm_Formalism_L2_DIV_b_pow_mem
-- name    : Formalism.L2.DIV.b_pow_mem
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T13:21:37.655833+00:00
-- url     : https://prove2.me/theorems/dbc9153b-5cf6-4119-83b5-eee2fdaa1f0c
-- title:
--   DIV: b pow mem
-- statement:
--   The DIV construction uses the b pow mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/DivisibilityProofs/TuplesP.lean#L902-L915
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/DivisibilityProofs/TuplesP.lean#L902-L915

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

theorem Formalism.L2.DIV.b_pow_mem (z : RInt F E) (hz : ∀ P : HeightOneSpectrum (𝓞 E), z ∈ P.asIdeal.map (toRInt F E))
    (I : Ideal (𝓞 E)) : I ≠ 0 → ∃ k : ℕ, z ^ k ∈ I.map (toRInt F E) := by sorry
