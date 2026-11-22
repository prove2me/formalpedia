-- Prove2me | Theorems.Thm_Formalism_FG_SolveVAux_low_neg
-- name    : Formalism.FG.SolveVAux.low_neg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:55:04.354037+00:00
-- url     : https://prove2.me/theorems/07cf36e1-c004-48c1-a142-d80a685e4f07
-- title:
--   Solve VAux: low neg
-- statement:
--   The Solve VAux construction uses the low neg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupWitt/FormalGroupWittProofs/SolveV.lean#L29-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupWitt/FormalGroupWittProofs/SolveV.lean#L29-L30

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

theorem Formalism.FG.SolveVAux.low_neg {N : ℕ} {p : MvPowerSeries τ R} (hp : Low N p) : Low N (-p) := by sorry
