-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_tableauBideterminant_canonical_eq_smul_highestWeight
-- name    : Formalism.InvariantFactorPaths.ColumnFamilies.tableauBideterminant_canonical_eq_smul_highestWeight
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T03:52:30.030872+00:00
-- url     : https://prove2.me/theorems/e19573f5-263b-4df3-af1f-0329a88226cc
-- title:
--   Column Families: tableau Bideterminant canonical eq smul highest Weight
-- statement:
--   The Column Families construction uses the tableau Bideterminant canonical eq smul highest Weight property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/EqSmulCanonicalOfUnipotentInvariant.lean#L233-L244
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/EqSmulCanonicalOfUnipotentInvariant.lean#L233-L244

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

theorem Formalism.InvariantFactorPaths.ColumnFamilies.tableauBideterminant_canonical_eq_smul_highestWeight (mu : Fin n → ℤ) : ∃ c0 : ℚ, c0 ≠ 0 ∧ qd_P mu (canT mu) = c0 • hw ℚ le_rfl (qd_nu mu) := by sorry
