-- Prove2me | Theorems.Thm_Formalism_G_LogP_eq_zero_of_pderiv_one
-- name    : Formalism.G.LogP.eq_zero_of_pderiv_one
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:05:11.990734+00:00
-- url     : https://prove2.me/theorems/bb61af22-57e1-4f2b-a083-2f16ccfb6da3
-- title:
--   Log P: eq zero of pderiv one
-- statement:
--   The Log P construction uses the eq zero of pderiv one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupLog/FormalGroupLogProofs/ConstantCoeffSubstOfZero.lean#L228-L252
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupLog/FormalGroupLogProofs/ConstantCoeffSubstOfZero.lean#L228-L252

import Definitions.Def_Formalism_FormalGroupLog_Statement
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ChainRule
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ConstantCoeffSubstOfZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPowerSeries
open Formalism Formalism.G Formalism.G.LogP
open Formalism.G.LogCR
variable {R : Type*} [CommRing R]

theorem Formalism.G.LogP.eq_zero_of_pderiv_one [Algebra ℚ R] {h : MvPowerSeries (Fin 2) R}
    (hD : MvPowerSeries.pderiv R 1 h = 0)
    (h0 : h.subst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) R), 0] = 0) : h = 0 := by sorry
