-- Prove2me | Theorems.Thm_Formalism_FG_SolveVAux_low_mul_sub
-- name    : Formalism.FG.SolveVAux.low_mul_sub
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:58:40.348771+00:00
-- url     : https://prove2.me/theorems/703cc6b6-caf4-4ad8-b359-d5b0157c3769
-- title:
--   Solve VAux: low mul sub
-- statement:
--   The Solve VAux construction uses the low mul sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupWitt/FormalGroupWittProofs/SolveV.lean#L58-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupWitt/FormalGroupWittProofs/SolveV.lean#L58-L64

import Definitions.Def_Formalism_FormalGroupWitt_SubstInjectiveV
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_SolveV
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
universe u v w
open Formalism Formalism.FG Formalism.FG.SolveVAux
open MvPowerSeries
variable {R : Type u} [CommRing R] {τ : Type w}

theorem Formalism.FG.SolveVAux.low_mul_sub {M : ℕ} {a a' b b' : MvPowerSeries τ R} (ha : Low M (a - a'))
    (hb : Low M (b - b')) : Low M (a * b - a' * b') := by sorry
