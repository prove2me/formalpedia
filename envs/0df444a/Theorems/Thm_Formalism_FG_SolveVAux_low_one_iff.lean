-- Prove2me | Theorems.Thm_Formalism_FG_SolveVAux_low_one_iff
-- name    : Formalism.FG.SolveVAux.low_one_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:14:43.62858+00:00
-- url     : https://prove2.me/theorems/1421734c-6f8a-4286-b640-cc36b8a512fb
-- title:
--   Solve VAux: low one iff
-- statement:
--   The Solve VAux construction uses the low one iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupWitt/FormalGroupWittProofs/SolveV.lean#L49-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupWitt/FormalGroupWittProofs/SolveV.lean#L49-L56

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

theorem Formalism.FG.SolveVAux.low_one_iff (p : MvPowerSeries τ R) : Low 1 p ↔ constantCoeff p = 0 := by sorry
