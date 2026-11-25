-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_uncurry_comp
-- name    : Formalism.L2.FormalSeriesBounds.uncurry_comp
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T00:37:19.891108+00:00
-- url     : https://prove2.me/theorems/9e3edc39-afbf-43ec-b95c-a98b7481a566
-- title:
--   Formal Series Bounds: uncurry comp
-- statement:
--   The Formal Series Bounds construction uses the uncurry comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTieCartFB.lean#L90-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTieCartFB.lean#L90-L100

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoeffAlongCvCongr
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieCartFB
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
variable {dd : ℕ}

theorem Formalism.L2.FormalSeriesBounds.uncurry_comp {φ a : Pt C 1 dd} (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0) (i : Fin dd) :
    MvPowerSeries.subst (fun j => un1 (a j)) (un1 (φ i)) = un1 (comp1 φ a i) := by sorry
