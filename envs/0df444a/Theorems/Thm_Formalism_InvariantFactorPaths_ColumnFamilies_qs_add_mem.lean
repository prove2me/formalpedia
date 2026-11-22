-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qs_add_mem
-- name    : Formalism.InvariantFactorPaths.ColumnFamilies.qs_add_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:31:56.298507+00:00
-- url     : https://prove2.me/theorems/569d0f48-bc3a-4c5b-b475-6d5b07432661
-- title:
--   Column Families: qs add mem
-- statement:
--   The Column Families construction uses the qs add mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/QsRemIffAdd.lean#L23-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/QsRemIffAdd.lean#L23-L24

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

theorem Formalism.InvariantFactorPaths.ColumnFamilies.qs_add_mem (D : Finset ℤ) (K : ℤ → Finset (Fin n)) (m : ↥D → Fin n) (c : ↥D) :
    qs_add D K m c.1 = insert (m c) (K c.1) := by sorry
