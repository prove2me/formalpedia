-- Prove2me | Theorems.Thm_Formalism_L2_DIV_finite_adele_is_unit
-- name    : Formalism.L2.DIV.finite_adele_is_unit
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T13:23:56.613911+00:00
-- url     : https://prove2.me/theorems/03759e0d-b361-4336-92b1-b5d34c4fdc73
-- title:
--   DIV: finite adele is unit
-- statement:
--   The DIV construction uses the finite adele is unit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/DivisibilityProofs/TuplesP.lean#L248-L257
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/DivisibilityProofs/TuplesP.lean#L248-L257

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
local notation "𝔸" => FiniteAdeleRing (𝓞 F) F

theorem Formalism.L2.DIV.finite_adele_is_unit (a : 𝔸) (h0 : ∀ v, a v ≠ 0)
    (h1 : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, Valued.v (a v) = 1) : IsUnit a := by sorry
