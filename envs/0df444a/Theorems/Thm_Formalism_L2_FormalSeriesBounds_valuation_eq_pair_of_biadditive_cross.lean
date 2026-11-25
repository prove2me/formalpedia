-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_valuation_eq_pair_of_biadditive_cross
-- name    : Formalism.L2.FormalSeriesBounds.valuation_eq_pair_of_biadditive_cross
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T09:46:32.662331+00:00
-- url     : https://prove2.me/theorems/50aba9ba-e191-450d-9434-bcf468927b6e
-- title:
--   Formal Series Bounds: valuation eq pair of biadditive cross
-- statement:
--   The Formal Series Bounds construction uses the valuation eq pair of biadditive cross property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/ValuationEqPairOfBiadditiveCross.lean#L78-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/ValuationEqPairOfBiadditiveCross.lean#L78-L81

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_TripleSubstSecondCoordinate
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ValuationEqPairOfBiadditiveCross
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
variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {d : ℕ} [NeZero d]
  {Orb : Type} [Fintype Orb] {I : Orb → Fin 2 → Type} [∀ o g, Fintype (I o g)]

theorem Formalism.L2.FormalSeriesBounds.valuation_eq_pair_of_biadditive_cross (Y : FBChart C V O dd) (p : ∀ o, PairData Y d (I o)) (H : ∀ o, (Y.raw (p o)).Hyps V)
    (Ls : LetSys C dd) (n : ℕ) (hP : ProjPullSt Y p) (hT : ∀ o, RawChart.TCoordSt (H o).cartH)
    (h1 : BiaddSt Y p) (h2 : CrossSt Y p) : ValEqPSt Y p H Ls n := by sorry
