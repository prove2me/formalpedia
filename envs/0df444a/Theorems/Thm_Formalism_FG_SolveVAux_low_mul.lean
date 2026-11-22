-- Prove2me | Theorems.Thm_Formalism_FG_SolveVAux_low_mul
-- name    : Formalism.FG.SolveVAux.low_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:14:36.706708+00:00
-- url     : https://prove2.me/theorems/c4561f5c-ea97-4d4d-9f63-ec880f1c4c17
-- title:
--   Solve VAux: low mul
-- statement:
--   The Solve VAux construction uses the low mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupWitt/FormalGroupWittProofs/SolveV.lean#L36-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupWitt/FormalGroupWittProofs/SolveV.lean#L36-L47

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

theorem Formalism.FG.SolveVAux.low_mul {M N : ℕ} {p q : MvPowerSeries τ R} (hp : Low M p) (hq : Low N q) :
    Low (M + N) (p * q) := by sorry
