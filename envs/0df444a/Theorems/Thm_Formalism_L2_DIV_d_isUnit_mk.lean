-- Prove2me | Theorems.Thm_Formalism_L2_DIV_d_isUnit_mk
-- name    : Formalism.L2.DIV.d_isUnit_mk
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T13:22:20.497228+00:00
-- url     : https://prove2.me/theorems/3ee3e0ab-4026-4069-a6d4-12f221f686dd
-- title:
--   DIV: d is Unit mk
-- statement:
--   The DIV construction uses the d is Unit mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/DivisibilityProofs/TuplesP.lean#L1442-L1453
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/DivisibilityProofs/TuplesP.lean#L1442-L1453

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

theorem Formalism.L2.DIV.d_isUnit_mk (P : HeightOneSpectrum (𝓞 E)) {b : 𝓞 E} (hb : b ∉ P.asIdeal) :
    IsUnit (Ideal.Quotient.mk P.asIdeal b) := by sorry
