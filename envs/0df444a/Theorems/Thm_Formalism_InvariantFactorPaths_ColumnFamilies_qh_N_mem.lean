-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qh_N_mem
-- name    : Formalism.InvariantFactorPaths.ColumnFamilies.qh_N_mem
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:19:22.289203+00:00
-- url     : https://prove2.me/theorems/2a2db43c-8177-4f9a-b342-3cf50de7961e
-- title:
--   Column Families: qh N mem
-- statement:
--   The Column Families construction uses the qh N mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/QhDetZpowMem.lean#L162-L191
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/QhDetZpowMem.lean#L162-L191

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_StatementH
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QhDetZpowMem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.ColumnFamilies
variable {n : ℕ} {R : Type} [CommRing R]

theorem Formalism.InvariantFactorPaths.ColumnFamilies.qh_N_mem (s : ℕ) (hs : s ≤ n) (J : Fin s → Fin n) :
    qhN R s hs J ∈ inducedSections R (fun a : Fin n => if a.val < s then 1 else 0) := by sorry
