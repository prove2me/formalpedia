-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qs_sum_choices
-- name    : Formalism.InvariantFactorPaths.ColumnFamilies.qs_sum_choices
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:52:09.061373+00:00
-- url     : https://prove2.me/theorems/b59911f0-34cb-4555-b30b-0cb82163405f
-- title:
--   Column Families: qs sum choices
-- statement:
--   The Column Families construction uses the qs sum choices property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/QsRemIffAdd.lean#L57-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/QsRemIffAdd.lean#L57-L70

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QsMnTranspose
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QsRemIffAdd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.ColumnFamilies
variable {n : ℕ}
variable {R : Type*} [CommRing R]

theorem Formalism.InvariantFactorPaths.ColumnFamilies.qs_sum_choices (S D : Finset ℤ) (hD : D ⊆ S) (u : ℤ → R) (p : ↥D → Fin n → Prop) [∀ c x, Decidable (p c x)]
    (s w : ↥D → Fin n → R) (F : (↥D → Fin n) → ℤ → R)
    (hF1 : ∀ m, ∀ c ∈ S \ D, F m c = u c) (hF2 : ∀ m (c : ↥D), F m c.1 = w c (m c))
    (v : ↥D → Fin n → R) :
    ∑ m : ↥D → Fin n, (if ∀ c, p c (m c) then (∏ c, s c (m c)) * (∏ c ∈ S, F m c) * ∏ c, v c (m c) else 0) =
      (∏ c ∈ S \ D, u c) * ∏ c : ↥D, ∑ x, if p c x then s c x * w c x * v c x else 0 := by sorry
