-- Prove2me | Theorems.Thm_Formalism_L2_DIV_c_inv_pow_mem
-- name    : Formalism.L2.DIV.c_inv_pow_mem
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T13:22:27.798808+00:00
-- url     : https://prove2.me/theorems/81b0e4db-0506-4f4b-a46f-4d50d4767968
-- title:
--   DIV: c inv pow mem
-- statement:
--   The DIV construction uses the c inv pow mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/DivisibilityProofs/TuplesP.lean#L522-L540
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/DivisibilityProofs/TuplesP.lean#L522-L540

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
local notation "ιE" => inclE (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)

theorem Formalism.L2.DIV.c_inv_pow_mem (x : (AfE F E)ˣ) (k : ℕ) : ∀ y ∈ (c_lat x) ^ k,
    ((x⁻¹ : (AfE F E)ˣ) : AfE F E) ^ k * ιE y ∈ RInt F E := by sorry
