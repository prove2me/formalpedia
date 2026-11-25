-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_comp_coordinate_point
-- name    : Formalism.L2.FormalSeriesBounds.comp_coordinate_point
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T00:45:05.530815+00:00
-- url     : https://prove2.me/theorems/a2089e80-ee46-43a5-b5c8-755c03194aa3
-- title:
--   Formal Series Bounds: comp coordinate point
-- statement:
--   The Formal Series Bounds construction uses the comp coordinate point property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTiePHStab.lean#L315-L320
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTiePHStab.lean#L315-L320

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieCartFB
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePHStab
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
open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ MvPowerSeries
variable {C : Type} [Field C]
variable {dd : ℕ}

theorem Formalism.L2.FormalSeriesBounds.comp_coordinate_point (φ : Pt C 1 dd) (g : Fin 2) (i : Fin dd) :
    comp1 φ (pt C (n := 2) dd g) i =
      MvPowerSeries.subst (fun q : Fin 1 × Fin dd => (X (g, q.2) : PS C 2 dd)) (φ i) := by sorry
