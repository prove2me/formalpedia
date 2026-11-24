-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_CharacteristicFromRanks_characteristic_of_rank_split
-- name    : Formalism.L2.FormalSeriesBounds.CharacteristicFromRanks.characteristic_of_rank_split
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:50:15.679985+00:00
-- url     : https://prove2.me/theorems/7806600d-fc6f-4ce4-a410-e4905f38f50c
-- title:
--   Characteristic From Ranks: characteristic of rank split
-- statement:
--   The Characteristic From Ranks construction uses the characteristic of rank split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/CharacteristicFromRanks.lean#L223-L280
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/CharacteristicFromRanks.lean#L223-L280

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_Interface
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ExistsStrictMonoMinor
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CharacteristicFromRanks
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
open Formalism.IncomingBounds
open Formalism.L2.FormalSeriesBounds.CharacteristicFromRanks
variable {C : Type} [Field C]

theorem Formalism.L2.FormalSeriesBounds.CharacteristicFromRanks.characteristic_of_rank_split {V : VF C} {d : ℕ} [NeZero d] {I J : Fin 2 → Type} [∀ g, Fintype (I g)]
    [∀ g, Fintype (J g)] (G : ∀ g, Cart V d (I g) (J g)) (n j j' rh r : ℕ)
    (r_eq : r = n + j + j') (big : Fin 2 → ZMod d → Prop)
    (big_compl : ∀ g a, big (1 - g) a ↔ ¬ big g a)
    (rk_big : ∀ g a, big g a → pT G g a = n + j)
    (rk_small : ∀ g a, ¬ big g a → pT G g a = j')
    (rk_fil : ∀ g a, (Finset.univ.filter fun κ : J g => (G g).ty (Sum.inr κ) = a).card + rh +
      pT G g a = r)
    (l_odd : V.l ≠ 2)
    (h : Fin 2 → ℕ) (hh : ∀ g, h g + rh = r)
    (ht : ∀ g, Fin (h g) → I g → C) (ht_int : ∀ g i x, V.Ge 0 (ht g i x))
    (l1 l2 : Fin 2 → ZMod d → ℝ)
    (hDET : ∀ g a, big g a → S4.CorDET V.l (pT G g) (l1 g) (l2 g) a)
    (hAi : ∀ g a, big g a → S4.ThmAi V.l r rh (pT G g) (l2 g) a)
    (hAiii : ∀ g a, big g a → ∃ e : Fin (pT G g a) ≃ {x : I g // (G g).ty (Sum.inl x) = a},
      S4.ThmAiii V.v (Matrix.of fun c i => ht g i (e c)) (l1 g a))
    (hGerm : ∀ g (i : Fin (h g)) (S : ∀ g, Sys (G g)) (t : ∀ g, I g → MvPowerSeries (I g) C),
      (∀ g, (S g).IsT (t g)) →
      upG g (mvExp (∑ x : I g, ht g i x • (MvPowerSeries.X x : MvPowerSeries (I g) C))) ∈
        IntGerm V t) :
    CHProp G n j j' big := by sorry
