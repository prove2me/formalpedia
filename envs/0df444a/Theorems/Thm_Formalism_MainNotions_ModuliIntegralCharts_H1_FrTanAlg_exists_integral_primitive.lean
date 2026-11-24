-- Prove2me | Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_FrTanAlg_exists_integral_primitive
-- name    : Formalism.MainNotions.ModuliIntegralCharts.H1.FrTanAlg.exists_integral_primitive
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T10:01:20.574728+00:00
-- url     : https://prove2.me/theorems/882ce7c0-f857-4a74-b62c-255f7c25993b
-- title:
--   Fr Tan Alg: exists integral primitive
-- statement:
--   The Fr Tan Alg construction uses the exists integral primitive property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/FrTanAlg.lean#L36-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/FrTanAlg.lean#L36-L50

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FrTanAlg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.FrTanAlg
open Polynomial NumberField
variable (E : Type) [Field E] [NumberField E]

theorem Formalism.MainNotions.ModuliIntegralCharts.H1.FrTanAlg.exists_integral_primitive : ∃ θ : 𝓞 E, IntermediateField.adjoin ℚ {(θ : E)} = ⊤ := by sorry
