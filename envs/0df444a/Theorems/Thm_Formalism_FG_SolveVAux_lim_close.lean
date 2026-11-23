-- Prove2me | Theorems.Thm_Formalism_FG_SolveVAux_lim_close
-- name    : Formalism.FG.SolveVAux.lim_close
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T01:24:01.451228+00:00
-- url     : https://prove2.me/theorems/1bfe5aa0-7c8d-4c98-b4cd-002f0a24b9b3
-- title:
--   Solve VAux: lim close
-- statement:
--   The Solve VAux construction uses the lim close property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupWitt/FormalGroupWittProofs/SolveV.lean#L249-L254
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupWitt/FormalGroupWittProofs/SolveV.lean#L249-L254

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

theorem Formalism.FG.SolveVAux.lim_close (hG : ∀ j, Low 1 (G j)) (hg : ∀ j, Low 2 (g j)) (n : ℕ) (i : ι) :
    Low n (lim G g i - seq G g n i) := by sorry
