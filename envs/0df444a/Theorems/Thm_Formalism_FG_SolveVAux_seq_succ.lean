-- Prove2me | Theorems.Thm_Formalism_FG_SolveVAux_seq_succ
-- name    : Formalism.FG.SolveVAux.seq_succ
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:18:13.377502+00:00
-- url     : https://prove2.me/theorems/2afcce61-ea5c-44f8-ad43-12a9eb1b17f4
-- title:
--   Solve VAux: seq succ
-- statement:
--   The Solve VAux construction uses the seq succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupWitt/FormalGroupWittProofs/SolveV.lean#L201-L203
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupWitt/FormalGroupWittProofs/SolveV.lean#L201-L203

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
variable {R : Type u} [CommRing R] {ι : Type v} [Finite ι] {τ : Type w}

theorem Formalism.FG.SolveVAux.seq_succ (G : ι → MvPowerSeries τ R) (g : ι → MvPowerSeries ι R) (n : ℕ) :
    seq G g (n + 1) = phi G g (seq G g n) := by sorry
