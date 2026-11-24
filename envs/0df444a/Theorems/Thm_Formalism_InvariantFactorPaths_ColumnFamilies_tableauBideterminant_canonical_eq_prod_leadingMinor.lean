-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_tableauBideterminant_canonical_eq_prod_leadingMinor
-- name    : Formalism.InvariantFactorPaths.ColumnFamilies.tableauBideterminant_canonical_eq_prod_leadingMinor
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:26:38.980248+00:00
-- url     : https://prove2.me/theorems/07405f92-ef3e-44cf-88a7-773e78a9f3bd
-- title:
--   Column Families: tableau Bideterminant canonical eq prod leading Minor
-- statement:
--   The Column Families construction uses the tableau Bideterminant canonical eq prod leading Minor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/EqSmulCanonicalOfUnipotentInvariant.lean#L226-L231
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/EqSmulCanonicalOfUnipotentInvariant.lean#L226-L231

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_FiltrationTheoremOfClauses
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalB
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_EqSmulCanonicalOfUnipotentInvariant
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
open Formalism.GradedWeylDivisibility
variable {n : ℕ}
variable [NeZero n]

theorem Formalism.InvariantFactorPaths.ColumnFamilies.tableauBideterminant_canonical_eq_prod_leadingMinor (mu : Fin n → ℤ) :
    qd_P mu (canT mu) = ∏ c : ↥(TCols mu), lpMinor ℚ (colH mu c) (colH_le mu c) (colH_le mu c) := by sorry
