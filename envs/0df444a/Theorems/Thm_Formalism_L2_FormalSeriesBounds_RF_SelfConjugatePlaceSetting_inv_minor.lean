-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_RF_SelfConjugatePlaceSetting_inv_minor
-- name    : Formalism.L2.FormalSeriesBounds.RF.SelfConjugatePlaceSetting.inv_minor
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T01:37:52.205108+00:00
-- url     : https://prove2.me/theorems/d86cd528-d85d-5a79-8b75-542f7ed47719
-- title:
--   Self Conjugate Place Setting: inv minor
-- statement:
--   The Self Conjugate Place Setting construction uses the inv minor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTieMemCInv.lean#L139-L160
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTieMemCInv.lean#L139-L160

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieMemC
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NormOneRowInvariant
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieMemCInv
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_RF_ConjugatePairPlaceSetting_inv_minor

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
variable {C : Type} [Field C] {V : VF C} {T : Type} {r : T → ℕ} {cc : T → T} {a : T → ℕ → ℕ}
  {Orb : Type} [Fintype Orb] {tau : Orb → ZMod 2 → T} {gm : Orb → ZMod 2 → Matrix (Fin 2) (Fin 2) C}
  {J : Orb → Fin 2 → Type} [∀ o g, Fintype (J o g)]
  {X : ∀ o, RowData C V 2 (fun _ => IIs r tau o) (J o)} {F : ∀ o, Flag (X o)}
  {gaC : Orb → ZMod 2 → ℕ → ℕ} {N : ℕ} {L : Orb → List (GlobalTheory 2 × ℝ)}
  {pl : (Σ o, Σ i : Fin (L o).length, Fin (rowsAt X L o i)) → Fin N} {n : ℕ} (plc : Fin N × Fin 2 ↪ Fin n)

theorem Formalism.L2.FormalSeriesBounds.RF.SelfConjugatePlaceSetting.inv_minor (H : SelfConjugatePlaceSetting r cc a tau gm X F gaC N L pl) (o : Orb) (g : Fin 2) (s : ZMod 2) {M : ℕ}
    (col : Fin M → Fin N) (k : ℕ) (σ : T) (i i' : Fin (r σ)) (hi : i' < i) (t : C) :
    rowShift r n C σ i i' t (PsiS r tau gm plc o col (rename ((F o).letter g s) (minorK C M ((X o).rkF g s) k))) =
      PsiS r tau gm plc o col (rename ((F o).letter g s) (minorK C M ((X o).rkF g s) k)) := by sorry
