-- Prove2me | Theorems.Thm_Formalism_L2_DIV_b_one_sub_eps_mem
-- name    : Formalism.L2.DIV.b_one_sub_eps_mem
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T13:22:23.064818+00:00
-- url     : https://prove2.me/theorems/3ef6353a-60f4-4433-9a00-1a7341d3190e
-- title:
--   DIV: b one sub eps mem
-- statement:
--   The DIV construction uses the b one sub eps mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/DivisibilityProofs/TuplesP.lean#L799-L805
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/DivisibilityProofs/TuplesP.lean#L799-L805

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

theorem Formalism.L2.DIV.b_one_sub_eps_mem (v : HeightOneSpectrum (𝓞 F)) (P : HeightOneSpectrum (𝓞 E))
    (hP : P.asIdeal.under (𝓞 F) = v.asIdeal) : 1 - bEps E v ∈ P.asIdeal.map (toRInt F E) := by sorry
