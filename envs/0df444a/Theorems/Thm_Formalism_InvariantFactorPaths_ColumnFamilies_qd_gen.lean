-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qd_gen
-- name    : Formalism.InvariantFactorPaths.ColumnFamilies.qd_gen
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:19:38.939297+00:00
-- url     : https://prove2.me/theorems/419c87d8-1d25-4a83-bc12-7148cc6bcf9d
-- title:
--   Column Families: qd gen
-- statement:
--   The Column Families construction uses the qd gen property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/TranslatesSpanCanonical.lean#L201-L220
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/TranslatesSpanCanonical.lean#L201-L220

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_EqSmulCanonicalOfUnipotentInvariant
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QcEvGLDetUZpow
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_TranslatesSpanCanonical
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

theorem Formalism.InvariantFactorPaths.ColumnFamilies.qd_gen (mu : Fin n → ℤ) (w : TIdx mu → ℚ) :
    ∃ w' ∈ Submodule.span ℚ (Set.range (qd_gcan mu)), qd_Lam mu w = qd_Lam mu w' := by sorry
