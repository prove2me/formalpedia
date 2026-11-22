-- Prove2me | Theorems.Thm_Formalism_FG_SolveVAux_low_zero
-- name    : Formalism.FG.SolveVAux.low_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:16:02.708799+00:00
-- url     : https://prove2.me/theorems/5d9bde73-be44-4302-939a-974c031134de
-- title:
--   Solve VAux: low zero
-- statement:
--   The Solve VAux construction uses the low zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupWitt/FormalGroupWittProofs/SolveV.lean#L18-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupWitt/FormalGroupWittProofs/SolveV.lean#L18-L18

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

theorem Formalism.FG.SolveVAux.low_zero (p : MvPowerSeries τ R) : Low 0 p := by sorry
