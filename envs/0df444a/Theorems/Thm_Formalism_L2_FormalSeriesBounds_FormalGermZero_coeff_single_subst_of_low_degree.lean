-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_FormalGermZero_coeff_single_subst_of_low_degree
-- name    : Formalism.L2.FormalSeriesBounds.FormalGermZero.coeff_single_subst_of_low_degree
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T00:56:19.684878+00:00
-- url     : https://prove2.me/theorems/35ce0493-6a1f-40c9-b249-9da23b01630b
-- title:
--   Formal Germ Zero: coeff single subst of low degree
-- statement:
--   The Formal Germ Zero construction uses the coeff single subst of low degree property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/CoeffSingleSubstOfLowDegree.lean#L98-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/CoeffSingleSubstOfLowDegree.lean#L98-L109

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_AbstractGermZeroCondition
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieCartAdd
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoeffSingleSubstOfLowDegree
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
open Formalism.L2.FormalSeriesBounds.FormalGermZero
open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
variable {C : Type} [Field C]

theorem Formalism.L2.FormalSeriesBounds.FormalGermZero.coeff_single_subst_of_low_degree {σ τ : Type} [Finite σ] (a : σ → MvPowerSeries τ C)
    (ha0 : ∀ s, MvPowerSeries.constantCoeff (a s) = 0) (r : MvPowerSeries σ C)
    (hr : ∀ e : σ →₀ ℕ, e.degree < 2 → MvPowerSeries.coeff e r = 0) (c : τ) :
    MvPowerSeries.coeff (Finsupp.single c 1) (MvPowerSeries.subst a r) = 0 := by sorry
