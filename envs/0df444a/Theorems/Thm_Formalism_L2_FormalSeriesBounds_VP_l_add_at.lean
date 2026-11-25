-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_VP_l_add_at
-- name    : Formalism.L2.FormalSeriesBounds.VP.l_add_at
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T10:37:18.912224+00:00
-- url     : https://prove2.me/theorems/fa9dc82c-cc39-5327-8fcc-257c92cf4800
-- title:
--   VP: l add at
-- statement:
--   The VP construction uses the l add at property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/ValueEquationOfProjectors.lean#L37-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/ValueEquationOfProjectors.lean#L37-L50

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

theorem Formalism.L2.FormalSeriesBounds.VP.l_add_at {u v : Fin dd → MvPowerSeries τ C} (hu : ∀ i, MvPowerSeries.constantCoeff (u i) = 0)
    (hv : ∀ i, MvPowerSeries.constantCoeff (v i) = 0) (m : Fin dd) :
    MvPowerSeries.subst (addAt Y u v) (l Y m) = MvPowerSeries.subst u (l Y m) + MvPowerSeries.subst v (l Y m) := by sorry
