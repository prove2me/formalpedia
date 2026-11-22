-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qs_rem_mem
-- name    : Formalism.InvariantFactorPaths.ColumnFamilies.qs_rem_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:31:40.737955+00:00
-- url     : https://prove2.me/theorems/3543e218-ed30-4f70-aa32-084324b071ab
-- title:
--   Column Families: qs rem mem
-- statement:
--   The Column Families construction uses the qs rem mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/QsRemIffAdd.lean#L17-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/QsRemIffAdd.lean#L17-L18

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

theorem Formalism.InvariantFactorPaths.ColumnFamilies.qs_rem_mem (D : Finset ℤ) (K : ℤ → Finset (Fin n)) (m : ↥D → Fin n) (c : ↥D) :
    qs_rem D K m c.1 = (K c.1).erase (m c) := by sorry
