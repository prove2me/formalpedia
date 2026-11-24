-- Prove2me | Theorems.Thm_Formalism_G_LogCR_pderiv_psubst
-- name    : Formalism.G.LogCR.pderiv_psubst
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:20:03.763559+00:00
-- url     : https://prove2.me/theorems/cef82e63-805d-465b-8958-316e316108ea
-- title:
--   Log CR: pderiv psubst
-- statement:
--   The Log CR construction uses the pderiv psubst property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupLog/FormalGroupLogProofs/ChainRule.lean#L115-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupLog/FormalGroupLogProofs/ChainRule.lean#L115-L120

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

theorem Formalism.G.LogCR.pderiv_psubst [Finite τ] {a : MvPowerSeries τ R} (ha : constantCoeff a = 0)
    (f : PowerSeries R) (i : τ) :
    MvPowerSeries.pderiv R i (f.subst a) =
      (PowerSeries.derivative R f).subst a * MvPowerSeries.pderiv R i a := by sorry
