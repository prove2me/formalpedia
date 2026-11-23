-- Prove2me | Theorems.Thm_Formalism_FG_SolveVAux_low_subst
-- name    : Formalism.FG.SolveVAux.low_subst
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:51:36.982806+00:00
-- url     : https://prove2.me/theorems/909f2dc1-5a15-4b04-9dcb-6daf47f84937
-- title:
--   Solve VAux: low subst
-- statement:
--   The Solve VAux construction uses the low subst property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupWitt/FormalGroupWittProofs/SolveV.lean#L144-L147
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupWitt/FormalGroupWittProofs/SolveV.lean#L144-L147

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

theorem Formalism.FG.SolveVAux.low_subst {k : ι → MvPowerSeries τ R} (hk : ∀ i, Low 1 (k i)) {p : MvPowerSeries ι R}
    (hp : Low 1 p) : Low 1 (subst k p) := by sorry
