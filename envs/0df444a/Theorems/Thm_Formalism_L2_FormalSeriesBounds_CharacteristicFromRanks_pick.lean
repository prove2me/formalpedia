-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_CharacteristicFromRanks_pick
-- name    : Formalism.L2.FormalSeriesBounds.CharacteristicFromRanks.pick
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:13:35.569174+00:00
-- url     : https://prove2.me/theorems/f7e15f11-2886-4f66-939c-51d3a5e9f91f
-- title:
--   Characteristic From Ranks: pick
-- statement:
--   The Characteristic From Ranks construction uses the pick property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/CharacteristicFromRanks.lean#L79-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/CharacteristicFromRanks.lean#L79-L103

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

theorem Formalism.L2.FormalSeriesBounds.CharacteristicFromRanks.pick (V : VF C) {ι : Type} [Fintype ι] (P : ι → Prop) {p n h : ℕ}
    (e : Fin p ≃ {x // P x}) (u : Fin n → ι → C) (hu : IsSat V u)
    (hsupp : ∀ c x, ¬ P x → u c x = 0) (ht : Fin h → ι → C) (ht_int : ∀ i x, V.Ge 0 (ht i x)) :
    ∃ (αR : Matrix (Fin p) (Fin h) (intR V)) (SR : Matrix (Fin n) (Fin p) (intR V))
      (WR : Matrix (Fin p) (Fin n) (intR V)), SR * WR = 1 ∧
      (∀ c i, (αR c i : C) = ht i (e c)) ∧
      ∀ f : Fin n → Fin h, vR V (Matrix.of fun k c => (SR * αR) c (f k)).det =
        V.v (Matrix.of fun ρ c : Fin n => ∑ x, ht (f ρ) x * u c x).det := by sorry
