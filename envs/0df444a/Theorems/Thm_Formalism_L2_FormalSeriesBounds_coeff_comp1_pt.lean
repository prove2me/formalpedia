-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_coeff_comp1_pt
-- name    : Formalism.L2.FormalSeriesBounds.coeff_comp1_pt
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T00:45:18.82574+00:00
-- url     : https://prove2.me/theorems/7229cb7b-3bb2-4960-a1ea-9e276c6c22da
-- title:
--   Formal Series Bounds: coeff comp1 pt
-- statement:
--   The Formal Series Bounds construction uses the coeff comp1 pt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTiePHStab.lean#L328-L337
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTiePHStab.lean#L328-L337

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

theorem Formalism.L2.FormalSeriesBounds.coeff_comp1_pt (φ : Pt C 1 dd) (g : Fin 2) (i k : Fin dd) :
    coeff (Finsupp.single (g, k) 1) (comp1 φ (pt C (n := 2) dd g) i) =
      coeff (Finsupp.single ((0 : Fin 1), k) 1) (φ i) := by sorry
