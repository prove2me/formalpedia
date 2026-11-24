-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_RF_valBlocks_of
-- name    : Formalism.L2.FormalSeriesBounds.RF.valBlocks_of
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T11:17:30.508856+00:00
-- url     : https://prove2.me/theorems/6a1e8e47-f726-4ed4-93d2-2c3120c9f72c
-- title:
--   RF: val Blocks of
-- statement:
--   The RF construction uses the val Blocks of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/BlockAdmissibleChart.lean#L42-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/BlockAdmissibleChart.lean#L42-L45

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockMembershipSelfConjugate
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieVal
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockAdmissibleChart
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
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds Formalism.L2.FormalSeriesBounds.RF
open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {d : ℕ} [NeZero d]
  {Orb : Type} [Fintype Orb] {I : Orb → Fin 2 → Type} [∀ o g, Fintype (I o g)]
  (Y : FBChart C V O dd) (p : ∀ o, PairData Y d (I o)) (H : ∀ o, (Y.raw (p o)).Hyps V) (Ls : LetSys C dd) (n : ℕ)
variable (F : ∀ o, Flag (rd Y p H o)) (Z : Finset Orb) (ga : Orb → Fin 2 → ZMod d → ℕ → ℕ)

theorem Formalism.L2.FormalSeriesBounds.RF.valBlocks_of (ν : ℝ) (hν : ∀ x ∈ Y.valSet Ls n, (ν : WithTop ℝ) ≤ x) (hs : PairsSep Y p)
    (hv : ValEqPSt Y p H Ls n) (hJ : JetProdSt) (hM : BlockMembershipChart Y p H Ls n F Z ga) (hA : BlockAdmissibleChart Y p H F Z ga) :
    ValBlocks (fun o => rd Y p H o) F Z n ga ν := by sorry
