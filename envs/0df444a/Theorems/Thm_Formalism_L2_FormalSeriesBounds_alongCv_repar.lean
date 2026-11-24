-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_alongCv_repar
-- name    : Formalism.L2.FormalSeriesBounds.alongCv_repar
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T11:34:38.913018+00:00
-- url     : https://prove2.me/theorems/4b009e70-e4cf-4a5c-b5ea-3d9360bf1ff6
-- title:
--   Formal Series Bounds: along Cv repar
-- statement:
--   The Formal Series Bounds construction uses the along Cv repar property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/ConstMemTypeSetOfNonneg.lean#L84-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/ConstMemTypeSetOfNonneg.lean#L84-L92

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieAxes
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ConstMemTypeSetOfNonneg
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
variable {C : Type} [Field C]

theorem Formalism.L2.FormalSeriesBounds.alongCv_repar {σ : Type} [Finite σ] {γ : σ → PowerSeries C}
    (hγ : ∀ i, PowerSeries.constantCoeff (γ i) = 0) {τ : PowerSeries C} (hτ : PowerSeries.constantCoeff τ = 0)
    (f : MvPowerSeries σ C) :
    alongCv (fun i => PowerSeries.subst τ (γ i)) f = PowerSeries.subst τ (alongCv γ f) := by sorry
