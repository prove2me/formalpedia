-- Prove2me | Theorems.Thm_Formalism_FG_SolveVAux_low_mono
-- name    : Formalism.FG.SolveVAux.low_mono
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:14:48.087282+00:00
-- url     : https://prove2.me/theorems/04a6f64c-6efe-4be1-813f-2a1f80859fba
-- title:
--   Solve VAux: low mono
-- statement:
--   The Solve VAux construction uses the low mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupWitt/FormalGroupWittProofs/SolveV.lean#L20-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupWitt/FormalGroupWittProofs/SolveV.lean#L20-L21

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

theorem Formalism.FG.SolveVAux.low_mono {M N : ℕ} (h : M ≤ N) {p : MvPowerSeries τ R} (hp : Low N p) : Low M p := by sorry
