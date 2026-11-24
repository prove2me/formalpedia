-- Prove2me | Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_PhiCMin_cj_mem_Dinv
-- name    : Formalism.MainNotions.ModuliIntegralCharts.H1.PhiCMin.cj_mem_Dinv
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T10:02:36.442861+00:00
-- url     : https://prove2.me/theorems/661b258c-5a0c-40c5-a13e-a6b1bf6bf88f
-- title:
--   Phi CMin: cj mem Dinv
-- statement:
--   The Phi CMin construction uses the cj mem Dinv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/PhiCMinA.lean#L162-L169
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/PhiCMinA.lean#L162-L169

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

theorem Formalism.MainNotions.ModuliIntegralCharts.H1.PhiCMin.cj_mem_Dinv {cj : E → E} (hcj : ∀ (φ : E →+* ℂ) (z : E), φ (cj z) = star (φ z))
    {z : E} (hz : z ∈ Dinv E) : cj z ∈ Dinv E := by sorry
