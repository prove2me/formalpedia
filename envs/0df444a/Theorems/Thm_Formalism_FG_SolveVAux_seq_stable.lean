-- Prove2me | Theorems.Thm_Formalism_FG_SolveVAux_seq_stable
-- name    : Formalism.FG.SolveVAux.seq_stable
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T18:40:58.301165+00:00
-- url     : https://prove2.me/theorems/9ef0791a-cdcb-4d9a-9662-2498236cacdc
-- title:
--   Solve VAux: seq stable
-- statement:
--   The Solve VAux construction uses the seq stable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupWitt/FormalGroupWittProofs/SolveV.lean#L235-L243
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupWitt/FormalGroupWittProofs/SolveV.lean#L235-L243

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

theorem Formalism.FG.SolveVAux.seq_stable (hG : ∀ j, Low 1 (G j)) (hg : ∀ j, Low 2 (g j)) (n m : ℕ) (hnm : n ≤ m)
    (i : ι) : Low n (seq G g m i - seq G g n i) := by sorry
