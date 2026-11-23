-- Prove2me | Theorems.Thm_Formalism_FG_SolveVAux_seq_step
-- name    : Formalism.FG.SolveVAux.seq_step
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T18:41:20.011072+00:00
-- url     : https://prove2.me/theorems/95963bdd-7b29-47fe-885e-8fc47f4a9ee5
-- title:
--   Solve VAux: seq step
-- statement:
--   The Solve VAux construction uses the seq step property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupWitt/FormalGroupWittProofs/SolveV.lean#L227-L233
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupWitt/FormalGroupWittProofs/SolveV.lean#L227-L233

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
variable {G : ι → MvPowerSeries τ R} {g : ι → MvPowerSeries ι R}

theorem Formalism.FG.SolveVAux.seq_step (hG : ∀ j, Low 1 (G j)) (hg : ∀ j, Low 2 (g j)) (n : ℕ) (i : ι) :
    Low n (seq G g (n + 1) i - seq G g n i) := by sorry
