-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_VP_subst_sum
-- name    : Formalism.L2.FormalSeriesBounds.VP.subst_sum
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T06:29:23.198037+00:00
-- url     : https://prove2.me/theorems/0ea515d0-484f-5e91-b0a1-add823e72769
-- title:
--   VP: subst sum
-- statement:
--   The VP construction uses the subst sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/SubstSubst.lean#L66-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/SubstSubst.lean#L66-L70

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LeafHolds
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieCartAdd
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LemmaMJet
import Definitions.Def_Formalism_DropLevelBounds_ConstantCoeffVanishing_UbintConstantCoeffEqZero
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_SubstSubst
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
open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open Formalism.L2.FormalSeriesBounds.VP
variable {C : Type} [Field C] {σ τ ρ : Type}

theorem Formalism.L2.FormalSeriesBounds.VP.subst_sum [Finite σ] {a : σ → MvPowerSeries τ C} (ha : ∀ s, MvPowerSeries.constantCoeff (a s) = 0)
    {ι : Type} (s : Finset ι) (F : ι → MvPowerSeries σ C) :
    MvPowerSeries.subst a (∑ i ∈ s, F i) = ∑ i ∈ s, MvPowerSeries.subst a (F i) := by sorry
