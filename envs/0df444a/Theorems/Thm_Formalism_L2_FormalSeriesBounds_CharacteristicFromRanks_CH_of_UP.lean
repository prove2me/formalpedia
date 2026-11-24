-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_CharacteristicFromRanks_CH_of_UP
-- name    : Formalism.L2.FormalSeriesBounds.CharacteristicFromRanks.CH_of_UP
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:55:54.997042+00:00
-- url     : https://prove2.me/theorems/457f9777-2851-4d81-bd10-da99c47dde9d
-- title:
--   Characteristic From Ranks: CH of UP
-- statement:
--   The Characteristic From Ranks construction uses the CH of UP property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/CharacteristicFromRanks.lean#L334-L355
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/CharacteristicFromRanks.lean#L334-L355

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

theorem Formalism.L2.FormalSeriesBounds.CharacteristicFromRanks.CH_of_UP {V : VF C} {d : ℕ} [NeZero d] {I J : Fin 2 → Type} [∀ g, Fintype (I g)]
    [∀ g, Fintype (J g)] (G : ∀ g, Cart V d (I g) (J g)) (n j j' : ℕ)
    (big : Fin 2 → ZMod d → Prop) (big_compl : ∀ g a, big (1 - g) a ↔ ¬ big g a)
    (h : Fin 2 → ℕ)
    (ht : ∀ g, Fin (h g) → I g → C) (ht_int : ∀ g i x, V.Ge 0 (ht g i x))
    (hUP : ∀ g a, big g a → ∃ e : Fin (pT G g a) ≃ {x : I g // (G g).ty (Sum.inl x) = a},
      ((Even d ∧ ∀ b : ZMod d, (big 0 b ↔ Even b.val)) →
        S4.lenCoker V.v (Matrix.of fun c i => ht g i (e c)) ≤
          ((upB V.l (n + j) j' (gam V.l) : ℝ) : WithTop ℝ)) ∧
      ((∀ b, big g b) →
        S4.lenCoker V.v (Matrix.of fun c i => ht g i (e c)) ≤ ((upB V.l (n + j) j' 0 : ℝ) : WithTop ℝ)))
    (hGerm : ∀ g (i : Fin (h g)) (S : ∀ g, Sys (G g)) (t : ∀ g, I g → MvPowerSeries (I g) C),
      (∀ g, (S g).IsT (t g)) →
      upG g (mvExp (∑ x : I g, ht g i x • (MvPowerSeries.X x : MvPowerSeries (I g) C))) ∈
        IntGerm V t) :
    CHProp G n j j' big := by sorry
