-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_VP_sumL_subst
-- name    : Formalism.L2.FormalSeriesBounds.VP.sumL_subst
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T10:30:32.298724+00:00
-- url     : https://prove2.me/theorems/d0bc6900-6859-48d6-a0e7-c4b724a5232e
-- title:
--   VP: sum L subst
-- statement:
--   The VP construction uses the sum L subst property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/ValueEquationOfProjectors.lean#L105-L114
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/ValueEquationOfProjectors.lean#L105-L114

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

theorem Formalism.L2.FormalSeriesBounds.VP.sumL_subst [Finite τ] {A : τ → MvPowerSeries τ' C} (hA : ∀ s, MvPowerSeries.constantCoeff (A s) = 0) :
    ∀ L : List (Fin dd → MvPowerSeries τ C), (∀ a ∈ L, GoodPt V a) → ∀ i,
      MvPowerSeries.subst A (sumL Y L i) = sumL Y (L.map fun a j => MvPowerSeries.subst A (a j)) i
  := by sorry
