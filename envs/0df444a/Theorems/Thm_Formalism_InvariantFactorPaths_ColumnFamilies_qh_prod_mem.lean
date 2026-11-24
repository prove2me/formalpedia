-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qh_prod_mem
-- name    : Formalism.InvariantFactorPaths.ColumnFamilies.qh_prod_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:23:02.051666+00:00
-- url     : https://prove2.me/theorems/b095d183-ced1-4d46-8632-49c83b9b43a1
-- title:
--   Column Families: qh prod mem
-- statement:
--   The Column Families construction uses the qh prod mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/QhDetZpowMem.lean#L116-L123
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/QhDetZpowMem.lean#L116-L123

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

theorem Formalism.InvariantFactorPaths.ColumnFamilies.qh_prod_mem {ι : Type*} (s : Finset ι) (f : ι → GLCoord R n) (m : ι → Fin n → ℤ)
    (h : ∀ i ∈ s, f i ∈ inducedSections R (m i)) : ∏ i ∈ s, f i ∈ inducedSections R (∑ i ∈ s, m i) := by sorry
