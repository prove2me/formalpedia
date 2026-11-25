-- Prove2me | Theorems.Thm_Formalism_FG_SolveVAux_lim_fixed
-- name    : Formalism.FG.SolveVAux.lim_fixed
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:41:07.549652+00:00
-- url     : https://prove2.me/theorems/dc22e76f-2d10-4f27-a070-0ab10d69935d
-- title:
--   Solve VAux: lim fixed
-- statement:
--   The Solve VAux construction uses the lim fixed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupWitt/FormalGroupWittProofs/SolveV.lean#L261-L269
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupWitt/FormalGroupWittProofs/SolveV.lean#L261-L269

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

theorem Formalism.FG.SolveVAux.lim_fixed (hG : ∀ j, Low 1 (G j)) (hg : ∀ j, Low 2 (g j)) (j : ι) :
    phi G g (lim G g) j = lim G g j := by sorry
