-- Prove2me | Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_PhiCMin_whiten_holds
-- name    : Formalism.MainNotions.ModuliIntegralCharts.H1.PhiCMin.whiten_holds
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:52:08.763732+00:00
-- url     : https://prove2.me/theorems/57535762-acfe-4976-801d-82628e2c6dbf
-- title:
--   Phi CMin: whiten holds
-- statement:
--   The Phi CMin construction uses the whiten holds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/PhiCMinC.lean#L11-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/PhiCMinC.lean#L11-L36

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_PhiCMinSt
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_PhiCMinC
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
open Matrix

theorem Formalism.MainNotions.ModuliIntegralCharts.H1.PhiCMin.whiten_holds : WhitenStatement := by sorry
