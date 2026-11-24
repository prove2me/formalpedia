-- Prove2me | Theorems.Thm_Formalism_L2_DIV_b_eps_mul
-- name    : Formalism.L2.DIV.b_eps_mul
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T13:22:46.760861+00:00
-- url     : https://prove2.me/theorems/61d96631-5f25-4197-ab7d-304a9de8862c
-- title:
--   DIV: b eps mul
-- statement:
--   The DIV construction uses the b eps mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/DivisibilityProofs/TuplesP.lean#L671-L679
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/DivisibilityProofs/TuplesP.lean#L671-L679

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

theorem Formalism.L2.DIV.b_eps_mul (v : HeightOneSpectrum (𝓞 F)) (z : AfE F E)
    (hz : ∀ v' : HeightOneSpectrum (𝓞 F), v' ≠ v → prV (E := E) v' z = 0) : afsplitEps E v * z = z := by sorry
