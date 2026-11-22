-- Prove2me | Theorems.Thm_Formalism_FG_SolveVAux_hasSubst_of_low
-- name    : Formalism.FG.SolveVAux.hasSubst_of_low
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:17:28.304431+00:00
-- url     : https://prove2.me/theorems/6cc11453-7f90-4b5d-82a5-60315ce583ca
-- title:
--   Solve VAux: has Subst of low
-- statement:
--   The Solve VAux construction uses the has Subst of low property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupWitt/FormalGroupWittProofs/SolveV.lean#L141-L142
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupWitt/FormalGroupWittProofs/SolveV.lean#L141-L142

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

theorem Formalism.FG.SolveVAux.hasSubst_of_low {k : ι → MvPowerSeries τ R} (hk : ∀ i, Low 1 (k i)) : HasSubst k := by sorry
