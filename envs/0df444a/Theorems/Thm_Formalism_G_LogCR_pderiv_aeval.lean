-- Prove2me | Theorems.Thm_Formalism_G_LogCR_pderiv_aeval
-- name    : Formalism.G.LogCR.pderiv_aeval
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:05:17.264838+00:00
-- url     : https://prove2.me/theorems/46081c60-e33e-4c45-b17f-4dee3c0f758c
-- title:
--   Log CR: pderiv aeval
-- statement:
--   The Log CR construction uses the pderiv aeval property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupLog/FormalGroupLogProofs/ChainRule.lean#L65-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupLog/FormalGroupLogProofs/ChainRule.lean#L65-L80

import Mathlib
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ChainRule
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
open Formalism Formalism.G Formalism.G.LogCR
variable {R : Type*} [CommRing R] {σ τ : Type*}

theorem Formalism.G.LogCR.pderiv_aeval [Fintype σ] (p : MvPolynomial σ R) (A : σ → MvPowerSeries τ R) (i : τ) :
    MvPowerSeries.pderiv R i (MvPolynomial.aeval A p) =
      ∑ j, MvPolynomial.aeval A (MvPolynomial.pderiv j p) * MvPowerSeries.pderiv R i (A j) := by sorry
