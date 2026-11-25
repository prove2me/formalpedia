-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_SelfConjugateGermZero_sat_self
-- name    : Formalism.L2.FormalSeriesBounds.SelfConjugateGermZero.sat_self
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T01:20:10.308344+00:00
-- url     : https://prove2.me/theorems/8e865d77-7d2c-498d-bc4d-c6917270ff08
-- title:
--   Self Conjugate Germ Zero: sat self
-- statement:
--   The Self Conjugate Germ Zero construction uses the sat self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/UncurryLogConstantCoeff.lean#L302-L330
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/UncurryLogConstantCoeff.lean#L302-L330

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
variable {d : ℕ} {I0 : Type} [Fintype I0]

theorem Formalism.L2.FormalSeriesBounds.SelfConjugateGermZero.sat_self (Y : FBChart C V O dd) (p : SelfData Y d I0) (g : Fin 2) :
    ∃ w : Fin 2 × Fin dd → I0 → C, (∀ x c, V.Ge 0 (w x c)) ∧
      ∀ c c' : I0, ∑ x, (Y.rawSelf p).u g c x * w x c' = if c = c' then 1 else 0 := by sorry
