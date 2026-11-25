-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_valuation_eq_pair_of_log_unit_germ
-- name    : Formalism.L2.FormalSeriesBounds.valuation_eq_pair_of_log_unit_germ
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T07:25:53.879017+00:00
-- url     : https://prove2.me/theorems/1ed4f1d6-58e0-5fbb-ae96-a863765128c4
-- title:
--   Formal Series Bounds: valuation eq pair of log unit germ
-- statement:
--   The Formal Series Bounds construction uses the valuation eq pair of log unit germ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/ValuationEqPairOfLogUnitGerm.lean#L98-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/ValuationEqPairOfLogUnitGerm.lean#L98-L101

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_IntSProd
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ValuationEqPairOfLogUnitGerm
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

theorem Formalism.L2.FormalSeriesBounds.valuation_eq_pair_of_log_unit_germ {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {d : ℕ}
    [NeZero d] {Orb : Type} [Fintype Orb] {I : Orb → Fin 2 → Type} [∀ o g, Fintype (I o g)]
    (Y : FBChart C V O dd) (p : ∀ o, PairData Y d (I o)) (H : ∀ o, (Y.raw (p o)).Hyps V) (Ls : LetSys C dd) (n : ℕ)
    (h1 : LogCoordSt Y p) (h2 : UnitSt Y p) (h3 : GermLiftSt Y p H) : ValEqPSt Y p H Ls n := by sorry
