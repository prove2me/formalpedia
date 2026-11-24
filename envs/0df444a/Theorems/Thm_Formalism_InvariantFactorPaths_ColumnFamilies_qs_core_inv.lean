-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qs_core_inv
-- name    : Formalism.InvariantFactorPaths.ColumnFamilies.qs_core_inv
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:27:29.963119+00:00
-- url     : https://prove2.me/theorems/b5ea6b9a-014b-43aa-a460-95ab67cd246e
-- title:
--   Column Families: qs core inv
-- statement:
--   The Column Families construction uses the qs core inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/QsRemIffAdd.lean#L119-L140
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/QsRemIffAdd.lean#L119-L140

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

theorem Formalism.InvariantFactorPaths.ColumnFamilies.qs_core_inv (g' : Matrix (Fin n) (Fin n) R) (hg : g * g' = 1) (S D : Finset ℤ) (hD : D ⊆ S)
    (J K : ℤ → Finset (Fin n)) (a : ↥D → Fin n) :
    ∑ m : ↥D → Fin n, (if ∀ c : ↥D, m c ∉ K c.1 then
        (∏ c : ↥D, ((qs_sg (K c.1) (m c) : ℤ) : R)) * (∏ c ∈ S, qs_mn g (J c) (qs_add D K m c)) *
          ∏ c : ↥D, g' (m c) (a c) else 0) =
      if ∀ c : ↥D, a c ∈ J c.1 then
        (∏ c : ↥D, ((qs_sg ((J c.1).erase (a c)) (a c) : ℤ) : R)) * ∏ c ∈ S, qs_mn g (qs_rem D J a c) (K c)
      else 0 := by sorry
