-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_RawChart_axes_of
-- name    : Formalism.L2.FormalSeriesBounds.RawChart.axes_of
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T11:06:22.271428+00:00
-- url     : https://prove2.me/theorems/55a37d8e-c728-4ac7-ab82-f03de6aa94d3
-- title:
--   Raw Chart: axes of
-- statement:
--   The Raw Chart construction uses the axes of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTieAxes.lean#L101-L114
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTieAxes.lean#L101-L114

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieFB
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieAxes
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X

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
open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ MvPowerSeries
variable {C : Type} [Field C]
open Formalism.L2.FormalSeriesBounds.RawChart
variable {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] {κ : Type} [Fintype κ] (X : RawChart C d I κ)

theorem Formalism.L2.FormalSeriesBounds.RawChart.axes_of (hex : ∀ x, constantCoeff (X.ex x) = 0)
    (hh : ∀ (g : Fin 2) (e : Fin 2 × κ →₀ ℕ), (∀ s ∈ e.support, s.1 ≠ g) → coeff e X.h = 0) : X.AxesSt := by sorry
