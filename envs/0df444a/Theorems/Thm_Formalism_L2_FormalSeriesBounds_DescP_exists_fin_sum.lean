-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_DescP_exists_fin_sum
-- name    : Formalism.L2.FormalSeriesBounds.DescP.exists_fin_sum
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T00:32:37.179477+00:00
-- url     : https://prove2.me/theorems/8c8b71ca-0006-41f1-a745-6f4aba4fc288
-- title:
--   Desc P: exists fin sum
-- statement:
--   The Desc P construction uses the exists fin sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTiePDescJet.lean#L207-L209
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTiePDescJet.lean#L207-L209

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieDesc
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePDescJet
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds Formalism.L2.FormalSeriesBounds.DescP
open MvPowerSeries Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

theorem Formalism.L2.FormalSeriesBounds.DescP.exists_fin_sum {α M : Type} [AddCommMonoid M] (s : Finset α) (g : α → M) :
    ∃ (N : ℕ) (e : Fin N → α), (∀ j, e j ∈ s) ∧ ∑ x ∈ s, g x = ∑ j, g (e j) := by sorry
