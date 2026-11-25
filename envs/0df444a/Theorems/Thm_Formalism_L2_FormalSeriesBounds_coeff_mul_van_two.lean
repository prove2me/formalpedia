-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_coeff_mul_van_two
-- name    : Formalism.L2.FormalSeriesBounds.coeff_mul_van_two
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T00:47:32.419939+00:00
-- url     : https://prove2.me/theorems/f3053f81-7ec4-4f65-abb7-14e65fd1a8fd
-- title:
--   Formal Series Bounds: coeff mul van two
-- statement:
--   The Formal Series Bounds construction uses the coeff mul van two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTiePHStab.lean#L76-L132
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTiePHStab.lean#L76-L132

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
variable {τ : Type}

theorem Formalism.L2.FormalSeriesBounds.coeff_mul_van_two {T1 T2 : Set τ} {F G : MvPowerSeries τ C} (hF : Van T1 F) (hG : Van T2 G) {P Q : τ}
    (hPQ : P ≠ Q) (hQ : Q ∉ T1) (hP : P ∉ T2) :
    coeff (E2 P Q) (F * G) = coeff (Finsupp.single P 1) F * coeff (Finsupp.single Q 1) G := by sorry
