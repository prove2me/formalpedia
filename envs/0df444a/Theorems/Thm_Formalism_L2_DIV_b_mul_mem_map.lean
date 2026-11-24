-- Prove2me | Theorems.Thm_Formalism_L2_DIV_b_mul_mem_map
-- name    : Formalism.L2.DIV.b_mul_mem_map
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T13:23:17.5168+00:00
-- url     : https://prove2.me/theorems/ecf78893-409f-495e-907f-12279959d358
-- title:
--   DIV: b mul mem map
-- statement:
--   The DIV construction uses the b mul mem map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/DivisibilityProofs/TuplesP.lean#L779-L786
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/DivisibilityProofs/TuplesP.lean#L779-L786

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

theorem Formalism.L2.DIV.b_mul_mem_map (P : Ideal (𝓞 E)) (c : 𝓞 E) (hc : c ∈ P) (t : RInt F E) :
    toRInt F E c * t ∈ P.map (toRInt F E) := by sorry
