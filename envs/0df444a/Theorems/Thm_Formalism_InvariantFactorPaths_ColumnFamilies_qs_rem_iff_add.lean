-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qs_rem_iff_add
-- name    : Formalism.InvariantFactorPaths.ColumnFamilies.qs_rem_iff_add
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:38:07.724257+00:00
-- url     : https://prove2.me/theorems/eaf6938d-4a08-4531-a65d-4c999af431c8
-- title:
--   Column Families: qs rem iff add
-- statement:
--   The Column Families construction uses the qs rem iff add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/QsRemIffAdd.lean#L29-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/QsRemIffAdd.lean#L29-L49

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

theorem Formalism.InvariantFactorPaths.ColumnFamilies.qs_rem_iff_add (D : Finset ℤ) (J K : ℤ → Finset (Fin n)) (m : ↥D → Fin n) :
    ((∀ c : ↥D, m c ∈ K c.1) ∧ J = qs_rem D K m) ↔ ((∀ c : ↥D, m c ∉ J c.1) ∧ K = qs_add D J m) := by sorry
