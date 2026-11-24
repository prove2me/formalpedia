-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qd_span_le
-- name    : Formalism.InvariantFactorPaths.ColumnFamilies.qd_span_le
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:20:46.715578+00:00
-- url     : https://prove2.me/theorems/d982b822-0d39-4cbf-8aae-a610b477349f
-- title:
--   Column Families: qd span le
-- statement:
--   The Column Families construction uses the qd span le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/EqSmulCanonicalOfUnipotentInvariant.lean#L122-L127
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/EqSmulCanonicalOfUnipotentInvariant.lean#L122-L127

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

theorem Formalism.InvariantFactorPaths.ColumnFamilies.qd_span_le (mu : Fin n → ℤ) :
    Submodule.span ℚ (Set.range fun I : TIdx mu => mapCoord ℚ (brk mu I)) ≤
      (dualWeyl ℚ n n (qd_nu mu)).map (qd_L mu) := by sorry
