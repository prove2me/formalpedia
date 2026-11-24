-- Prove2me | Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_PhiCMin_cj_ratCast
-- name    : Formalism.MainNotions.ModuliIntegralCharts.H1.PhiCMin.cj_ratCast
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T10:02:35.314801+00:00
-- url     : https://prove2.me/theorems/c493ae8f-0a27-479d-9855-d6cd95a76915
-- title:
--   Phi CMin: cj rat Cast
-- statement:
--   The Phi CMin construction uses the cj rat Cast property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/PhiCMinA.lean#L58-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/PhiCMinA.lean#L58-L58

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_PhiCMinA
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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.PhiCMin
open NumberField Module FractionalIdeal
open scoped nonZeroDivisors
variable {E : Type} [Field E] [NumberField E]
variable {cj : E → E} (hcj : ∀ (φ : E →+* ℂ) (z : E), φ (cj z) = star (φ z))
include hcj

theorem Formalism.MainNotions.ModuliIntegralCharts.H1.PhiCMin.cj_ratCast (q : ℚ) : cj (q : E) = q := by sorry
