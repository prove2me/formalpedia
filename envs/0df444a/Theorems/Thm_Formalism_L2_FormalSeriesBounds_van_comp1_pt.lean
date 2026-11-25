-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_van_comp1_pt
-- name    : Formalism.L2.FormalSeriesBounds.van_comp1_pt
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T00:44:47.543545+00:00
-- url     : https://prove2.me/theorems/db96c4d9-f8b8-4a8b-8d6f-e54b6eca71ac
-- title:
--   Formal Series Bounds: van comp1 pt
-- statement:
--   The Formal Series Bounds construction uses the van comp1 pt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTiePHStab.lean#L322-L326
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTiePHStab.lean#L322-L326

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieCartFB
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePHStab
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
variable {dd : ℕ}

theorem Formalism.L2.FormalSeriesBounds.van_comp1_pt {φ : Pt C 1 dd} (hφ : ∀ i, constantCoeff (φ i) = 0) (g : Fin 2) (i : Fin dd) :
    Van (Tg dd g) (comp1 φ (pt C (n := 2) dd g) i) := by sorry
