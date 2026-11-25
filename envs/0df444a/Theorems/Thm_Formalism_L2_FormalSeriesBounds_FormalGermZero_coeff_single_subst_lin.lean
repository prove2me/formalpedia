-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_FormalGermZero_coeff_single_subst_lin
-- name    : Formalism.L2.FormalSeriesBounds.FormalGermZero.coeff_single_subst_lin
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T00:55:56.579005+00:00
-- url     : https://prove2.me/theorems/0b87d427-9dc1-4679-a889-31ca68035d95
-- title:
--   Formal Germ Zero: coeff single subst lin
-- statement:
--   The Formal Germ Zero construction uses the coeff single subst lin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/CoeffSingleSubstOfLowDegree.lean#L111-L123
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/CoeffSingleSubstOfLowDegree.lean#L111-L123

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_AbstractGermZeroCondition
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieCartAdd
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoeffSingleSubstOfLowDegree
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X
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

theorem Formalism.L2.FormalSeriesBounds.FormalGermZero.coeff_single_subst_lin {σ τ : Type} [Finite σ] (a : σ → MvPowerSeries τ C)
    (ha0 : ∀ s, MvPowerSeries.constantCoeff (a s) = 0) (f : MvPowerSeries σ C) (i : σ)
    (hf : ∀ μ : σ →₀ ℕ, μ.degree ≤ 1 → MvPowerSeries.coeff μ f = MvPowerSeries.coeff μ (MvPowerSeries.X i))
    (c : τ) :
    MvPowerSeries.coeff (Finsupp.single c 1) (MvPowerSeries.subst a f) =
      MvPowerSeries.coeff (Finsupp.single c 1) (a i) := by sorry
