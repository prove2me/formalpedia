-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_SelfConjugateGermZero_hasSubst_col
-- name    : Formalism.L2.FormalSeriesBounds.SelfConjugateGermZero.hasSubst_col
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T01:18:04.21779+00:00
-- url     : https://prove2.me/theorems/0e1c392d-a412-4a21-accc-3d5a6b687480
-- title:
--   Self Conjugate Germ Zero: has Subst col
-- statement:
--   The Self Conjugate Germ Zero construction uses the has Subst col property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/UncurryLogConstantCoeff.lean#L33-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/UncurryLogConstantCoeff.lean#L33-L34

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_GeneralGermZero
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieSelf
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_UncurryLogConstantCoeff
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
open Formalism.L2.FormalSeriesBounds.SelfConjugateGermZero
open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ FormalGermZero GeneralGermZero
variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ}

theorem Formalism.L2.FormalSeriesBounds.SelfConjugateGermZero.hasSubst_col (col : Fin 2) :
    MvPowerSeries.HasSubst (fun x : Fin dd => (MvPowerSeries.X (col, x) : MvPowerSeries (Fin 2 × Fin dd) C)) := by sorry
