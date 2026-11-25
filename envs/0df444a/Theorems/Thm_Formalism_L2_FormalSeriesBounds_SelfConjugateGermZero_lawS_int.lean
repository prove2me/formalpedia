-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_SelfConjugateGermZero_lawS_int
-- name    : Formalism.L2.FormalSeriesBounds.SelfConjugateGermZero.lawS_int
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T01:11:50.98763+00:00
-- url     : https://prove2.me/theorems/e250e860-f3ac-42ea-8b82-5dd76d4d8ee0
-- title:
--   Self Conjugate Germ Zero: law S int
-- statement:
--   The Self Conjugate Germ Zero construction uses the law S int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/UncurryLogConstantCoeff.lean#L49-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/UncurryLogConstantCoeff.lean#L49-L53

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_GeneralGermZero
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieSelf
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_UncurryLogConstantCoeff
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

theorem Formalism.L2.FormalSeriesBounds.SelfConjugateGermZero.lawS_int (Y : FBChart C V O dd) (x : Fin 2 × Fin dd) : IntS V (lawS Y x) := by sorry
