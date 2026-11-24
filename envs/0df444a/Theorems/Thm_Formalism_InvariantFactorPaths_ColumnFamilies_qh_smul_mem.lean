-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qh_smul_mem
-- name    : Formalism.InvariantFactorPaths.ColumnFamilies.qh_smul_mem
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:19:34.24627+00:00
-- url     : https://prove2.me/theorems/6c8b9c49-f775-4dac-b257-1c501000c000
-- title:
--   Column Families: qh smul mem
-- statement:
--   The Column Families construction uses the qh smul mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/QhDetZpowMem.lean#L90-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/QhDetZpowMem.lean#L90-L94

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

theorem Formalism.InvariantFactorPaths.ColumnFamilies.qh_smul_mem {mu : Fin n → ℤ} (r : R) {f : GLCoord R n} (hf : f ∈ inducedSections R mu) :
    r • f ∈ inducedSections R mu := by sorry
