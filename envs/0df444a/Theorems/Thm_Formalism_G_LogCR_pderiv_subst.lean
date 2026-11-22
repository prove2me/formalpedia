-- Prove2me | Theorems.Thm_Formalism_G_LogCR_pderiv_subst
-- name    : Formalism.G.LogCR.pderiv_subst
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T22:20:14.615831+00:00
-- url     : https://prove2.me/theorems/47872fde-35bd-4299-9409-8c4c02e4a695
-- title:
--   Log CR: pderiv subst
-- statement:
--   The Log CR construction uses the pderiv subst property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupLog/FormalGroupLogProofs/ChainRule.lean#L82-L113
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupLog/FormalGroupLogProofs/ChainRule.lean#L82-L113

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

theorem Formalism.G.LogCR.pderiv_subst [Fintype σ] [Finite τ] {a : σ → MvPowerSeries τ R}
    (ha : ∀ j, constantCoeff (a j) = 0) (f : MvPowerSeries σ R) (i : τ) :
    MvPowerSeries.pderiv R i (f.subst a) =
      ∑ j, (MvPowerSeries.pderiv R j f).subst a * MvPowerSeries.pderiv R i (a j) := by sorry
