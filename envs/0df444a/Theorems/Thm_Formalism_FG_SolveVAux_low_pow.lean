-- Prove2me | Theorems.Thm_Formalism_FG_SolveVAux_low_pow
-- name    : Formalism.FG.SolveVAux.low_pow
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:15:12.285791+00:00
-- url     : https://prove2.me/theorems/e4187de3-02a8-4e23-a79f-729e9f936dc5
-- title:
--   Solve VAux: low pow
-- statement:
--   The Solve VAux construction uses the low pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupWitt/FormalGroupWittProofs/SolveV.lean#L85-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupWitt/FormalGroupWittProofs/SolveV.lean#L85-L88

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
variable {R : Type u} [CommRing R] {ι : Type v} {τ : Type w}

theorem Formalism.FG.SolveVAux.low_pow {p : MvPowerSeries τ R} (hp : Low 1 p) (n : ℕ) : Low n (p ^ n) := by sorry
