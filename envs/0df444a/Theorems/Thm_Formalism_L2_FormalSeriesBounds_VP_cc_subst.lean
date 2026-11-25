-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_VP_cc_subst
-- name    : Formalism.L2.FormalSeriesBounds.VP.cc_subst
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T06:17:08.128021+00:00
-- url     : https://prove2.me/theorems/14d8c54c-3f7c-4aa8-88e2-7a53674b548b
-- title:
--   VP: cc subst
-- statement:
--   The VP construction uses the cc subst property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/SubstSubst.lean#L43-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/SubstSubst.lean#L43-L49

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

theorem Formalism.L2.FormalSeriesBounds.VP.cc_subst [Finite σ] {a : σ → MvPowerSeries τ C} (ha : ∀ s, MvPowerSeries.constantCoeff (a s) = 0)
    {f : MvPowerSeries σ C} (hf : MvPowerSeries.constantCoeff f = 0) :
    MvPowerSeries.constantCoeff (MvPowerSeries.subst a f) = 0 := by sorry
