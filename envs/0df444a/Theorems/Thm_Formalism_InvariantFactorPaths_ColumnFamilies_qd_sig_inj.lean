-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qd_sig_inj
-- name    : Formalism.InvariantFactorPaths.ColumnFamilies.qd_sig_inj
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T03:48:46.194351+00:00
-- url     : https://prove2.me/theorems/35657e71-bd34-4045-b403-9e7961d23ea9
-- title:
--   Column Families: qd sig inj
-- statement:
--   The Column Families construction uses the qd sig inj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/EqSmulCanonicalOfUnipotentInvariant.lean#L42-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/EqSmulCanonicalOfUnipotentInvariant.lean#L42-L49

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

theorem Formalism.InvariantFactorPaths.ColumnFamilies.qd_sig_inj (n : ℕ) : Function.Injective (qd_sig n) := by sorry
