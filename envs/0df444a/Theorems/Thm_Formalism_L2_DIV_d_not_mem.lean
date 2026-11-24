-- Prove2me | Theorems.Thm_Formalism_L2_DIV_d_not_mem
-- name    : Formalism.L2.DIV.d_not_mem
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T13:22:19.718951+00:00
-- url     : https://prove2.me/theorems/74fd43ad-288d-4f30-8a6c-35515aa17515
-- title:
--   DIV: d not mem
-- statement:
--   The DIV construction uses the d not mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/DivisibilityProofs/TuplesP.lean#L1462-L1473
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/DivisibilityProofs/TuplesP.lean#L1462-L1473

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
set_option quotPrecheck false in
local notation "uIn" => Units.map (RInt F E).subtype.toMonoidHom

theorem Formalism.L2.DIV.d_not_mem (hC : TpComap) (P : HeightOneSpectrum (𝓞 E)) (u : (RInt F E)ˣ) (b : 𝓞 E)
    (h : (u : RInt F E) - toRInt F E b ∈ P.asIdeal.map (toRInt F E)) : b ∉ P.asIdeal := by sorry
