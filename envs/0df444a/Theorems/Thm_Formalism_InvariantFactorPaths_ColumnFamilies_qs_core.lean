-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qs_core
-- name    : Formalism.InvariantFactorPaths.ColumnFamilies.qs_core
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:20:52.419356+00:00
-- url     : https://prove2.me/theorems/22806833-8ae5-42a7-aab3-51ae54ef4de0
-- title:
--   Column Families: qs core
-- statement:
--   The Column Families construction uses the qs core property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/QsRemIffAdd.lean#L74-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/QsRemIffAdd.lean#L74-L97

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
variable (g : Matrix (Fin n) (Fin n) R)

theorem Formalism.InvariantFactorPaths.ColumnFamilies.qs_core (S D : Finset ℤ) (hD : D ⊆ S) (J K : ℤ → Finset (Fin n)) (a : ↥D → Fin n) :
    ∑ m : ↥D → Fin n, (if ∀ c : ↥D, m c ∈ K c.1 then
        (∏ c : ↥D, ((qs_sg ((K c.1).erase (m c)) (m c) : ℤ) : R)) * (∏ c ∈ S, qs_mn g (J c) (qs_rem D K m c)) *
          ∏ c : ↥D, g (a c) (m c) else 0) =
      if ∀ c : ↥D, a c ∉ J c.1 then
        (∏ c : ↥D, ((qs_sg (J c.1) (a c) : ℤ) : R)) * ∏ c ∈ S, qs_mn g (qs_add D J a c) (K c) else 0 := by sorry
