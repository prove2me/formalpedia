-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_valuation_eq_pair_of_unit_germ
-- name    : Formalism.L2.FormalSeriesBounds.valuation_eq_pair_of_unit_germ
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T08:22:40.717927+00:00
-- url     : https://prove2.me/theorems/74c237f8-7952-5e2e-a4a2-c2f8de0f65f2
-- title:
--   Formal Series Bounds: valuation eq pair of unit germ
-- statement:
--   The Formal Series Bounds construction uses the valuation eq pair of unit germ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/ValuationEqPairOfUnitGerm.lean#L244-L248
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/ValuationEqPairOfUnitGerm.lean#L244-L248

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_PullbackLogCoordsEvalZero
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieCartFB
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ValuationEqPairOfUnitGerm
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
open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj

theorem Formalism.L2.FormalSeriesBounds.valuation_eq_pair_of_unit_germ {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {d : ℕ}
    [NeZero d] {Orb : Type} [Fintype Orb] {I : Orb → Fin 2 → Type} [∀ o g, Fintype (I o g)]
    (Y : FBChart C V O dd) (p : ∀ o, PairData Y d (I o)) (H : ∀ o, (Y.raw (p o)).Hyps V) (Ls : LetSys C dd) (n : ℕ)
    (h2 : UnitSt Y p) (h3 : GermLiftSt Y p H) : ValEqPSt Y p H Ls n := by sorry
