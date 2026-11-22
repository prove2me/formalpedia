-- Prove2me | Theorems.Thm_Formalism_FG_SolveVAux_P_single
-- name    : Formalism.FG.SolveVAux.P_single
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:16:01.825857+00:00
-- url     : https://prove2.me/theorems/71c0f97e-b8b2-467d-9b48-175f4301af6b
-- title:
--   Solve VAux: P single
-- statement:
--   The Solve VAux construction uses the P single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupWitt/FormalGroupWittProofs/SolveV.lean#L79-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupWitt/FormalGroupWittProofs/SolveV.lean#L79-L81

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

theorem Formalism.FG.SolveVAux.P_single (k : ι → MvPowerSeries τ R) (i : ι) (n : ℕ) :
    P k (Finsupp.single i n) = k i ^ n := by sorry
