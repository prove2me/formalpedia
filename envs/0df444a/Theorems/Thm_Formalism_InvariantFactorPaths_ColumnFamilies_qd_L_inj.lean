-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qd_L_inj
-- name    : Formalism.InvariantFactorPaths.ColumnFamilies.qd_L_inj
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:21:58.598845+00:00
-- url     : https://prove2.me/theorems/07921cbb-8f75-40f0-b9da-03366e000e9e
-- title:
--   Column Families: qd L inj
-- statement:
--   The Column Families construction uses the qd L inj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/TranslatesSpanCanonical.lean#L170-L175
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/TranslatesSpanCanonical.lean#L170-L175

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

theorem Formalism.InvariantFactorPaths.ColumnFamilies.qd_L_inj (mu : Fin n → ℤ) (P Q : MvPolynomial (Fin n × Fin n) ℚ)
    (h : evGLR (R := ℚ) (qd_genPt n) (qd_L mu P) = evGLR (R := ℚ) (qd_genPt n) (qd_L mu Q)) : P = Q := by sorry
