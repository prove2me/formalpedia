-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_RF_ConjugatePairPlaceSetting_inv_bi
-- name    : Formalism.L2.FormalSeriesBounds.RF.ConjugatePairPlaceSetting.inv_bi
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T00:47:23.829276+00:00
-- url     : https://prove2.me/theorems/062f7af5-4696-4f9e-a79a-7903eac2e96f
-- title:
--   Conjugate Pair Place Setting: inv bi
-- statement:
--   The Conjugate Pair Place Setting construction uses the inv bi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/NormOneRowInvariant.lean#L130-L138
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/NormOneRowInvariant.lean#L130-L138

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockMembershipNormOne
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NormOneRowInvariant
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
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds Formalism.L2.FormalSeriesBounds.RF
open Formalism.IncomingBounds Formalism.L2.Pj MvPolynomial
variable {C : Type} [Field C] {V : VF C} {d : ℕ} [NeZero d] {T : Type} {r : T → ℕ} {cc : T → T} {a : T → ℕ → ℕ}
  {Orb : Type} [Fintype Orb] {tau : Orb → Fin 2 → ZMod d → T} {J : Orb → Fin 2 → Type} [∀ o g, Fintype (J o g)]
  {X : ∀ o, RowData C V d (IIof r tau o) (J o)} {F : ∀ o, Flag (X o)} {Z : Finset Orb}
  {ga : Orb → Fin 2 → ZMod d → ℕ → ℕ} {n : ℕ} {L : Orb → List (GlobalTheory d × ℝ)}
  {pl : (Σ o, Σ i : Fin (L o).length, Fin (rowsAt X L o i)) → Fin n}

theorem Formalism.L2.FormalSeriesBounds.RF.ConjugatePairPlaceSetting.inv_bi (H : ConjugatePairPlaceSetting r cc a tau X F Z ga n L pl) (o : Orb) (g g' : Fin 2) (s s' : ZMod d) {N : ℕ}
    (col : Fin N → Fin n) (k e1 e2 : ℕ) (σ : T) (i i' : Fin (r σ)) (hi : i' < i) (t : C) :
    rowShift r n C σ i i' t (rename (psiL r tau n o col)
      (rename ((F o).letter g s) (minorK C N ((X o).rkF g s) k) ^ e1 *
        rename ((F o).letter g' s') (minorK C N ((X o).rkF g' s') k) ^ e2)) =
      rename (psiL r tau n o col)
      (rename ((F o).letter g s) (minorK C N ((X o).rkF g s) k) ^ e1 *
        rename ((F o).letter g' s') (minorK C N ((X o).rkF g' s') k) ^ e2) := by sorry
