-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_VP_e_lAt
-- name    : Formalism.L2.FormalSeriesBounds.VP.e_lAt
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T10:25:14.574224+00:00
-- url     : https://prove2.me/theorems/1668a039-4c72-5bbb-b986-795a6b6752eb
-- title:
--   VP: e l At
-- statement:
--   The VP construction uses the e l At property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/ValueEquationOfProjectors.lean#L57-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/ValueEquationOfProjectors.lean#L57-L59

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoordinateChangeComp1IntertwinesAction
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ValueEquationOfProjectors
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Van_subst

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj
open Formalism.L2.FormalSeriesBounds.VP
variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {τ τ' : Type}
variable (Y : FBChart C V O dd)

theorem Formalism.L2.FormalSeriesBounds.VP.e_lAt {P : Fin dd → MvPowerSeries τ C} (hP : ∀ i, MvPowerSeries.constantCoeff (P i) = 0) (i : Fin dd) :
    MvPowerSeries.subst (fun m => MvPowerSeries.subst P (l Y m)) (e Y i) = P i := by sorry
