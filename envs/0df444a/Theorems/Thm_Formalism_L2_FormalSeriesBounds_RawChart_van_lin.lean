-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_RawChart_van_lin
-- name    : Formalism.L2.FormalSeriesBounds.RawChart.van_lin
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T11:07:28.291803+00:00
-- url     : https://prove2.me/theorems/7d74613e-012f-4914-a667-8c1df14c539d
-- title:
--   Raw Chart: van lin
-- statement:
--   The Raw Chart construction uses the van lin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTieAxes.lean#L69-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTieAxes.lean#L69-L77

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

theorem Formalism.L2.FormalSeriesBounds.RawChart.van_lin (g : Fin 2) (b : I g → C) :
    Van {w : WV I | w.1 = g} (∑ c : I g, b c • (MvPowerSeries.X (⟨g, c⟩ : WV I) : MvPowerSeries (WV I) C)) := by sorry
