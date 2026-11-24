-- Prove2me | Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_PhiCMin_trace_cj
-- name    : Formalism.MainNotions.ModuliIntegralCharts.H1.PhiCMin.trace_cj
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T10:02:32.30356+00:00
-- url     : https://prove2.me/theorems/7def7af2-7379-4d65-b70f-4b32d9d9d585
-- title:
--   Phi CMin: trace cj
-- statement:
--   The Phi CMin construction uses the trace cj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/PhiCMinA.lean#L48-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/PhiCMinA.lean#L48-L53

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

theorem Formalism.MainNotions.ModuliIntegralCharts.H1.PhiCMin.trace_cj (z : E) : Algebra.trace ℚ E (cj z) = Algebra.trace ℚ E z := by sorry
