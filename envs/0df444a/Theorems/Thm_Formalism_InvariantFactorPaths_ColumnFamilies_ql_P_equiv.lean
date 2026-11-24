-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_ql_P_equiv
-- name    : Formalism.InvariantFactorPaths.ColumnFamilies.ql_P_equiv
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:19:47.007866+00:00
-- url     : https://prove2.me/theorems/90eb276c-14c1-4b65-8acf-b4ca70354649
-- title:
--   Column Families: ql P equiv
-- statement:
--   The Column Families construction uses the ql P equiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/LWedge.lean#L100-L128
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/LWedge.lean#L100-L128

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_LaplaceExpansionColumn
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_LWedge
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

theorem Formalism.InvariantFactorPaths.ColumnFamilies.ql_P_equiv {N : ℕ} (k : Fin N → Finset (Fin n)) (L : Finset (Fin n)) (i : Fin N → Finset (Fin n)) :
    ∑ k' : Fin N → Finset (Fin n), ∑ L', (∏ j, qs_mn g (k j) (k' j)) * qs_mn g L L' * ql_P R k' L' i =
      ∑ i' : Fin N → Finset (Fin n), ql_P R k L i' * ∏ j, qs_mn g (i' j) (i j) := by sorry
