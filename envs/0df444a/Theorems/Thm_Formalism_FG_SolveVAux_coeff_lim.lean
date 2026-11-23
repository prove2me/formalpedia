-- Prove2me | Theorems.Thm_Formalism_FG_SolveVAux_coeff_lim
-- name    : Formalism.FG.SolveVAux.coeff_lim
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:41:21.534958+00:00
-- url     : https://prove2.me/theorems/48227262-e452-424d-aa0b-fb9837ff99f0
-- title:
--   Solve VAux: coeff lim
-- statement:
--   The Solve VAux construction uses the coeff lim property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupWitt/FormalGroupWittProofs/SolveV.lean#L245-L247
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupWitt/FormalGroupWittProofs/SolveV.lean#L245-L247

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

theorem Formalism.FG.SolveVAux.coeff_lim (d : τ →₀ ℕ) (i : ι) :
    coeff d (lim G g i) = coeff d (seq G g (d.degree + 1) i) := by sorry
