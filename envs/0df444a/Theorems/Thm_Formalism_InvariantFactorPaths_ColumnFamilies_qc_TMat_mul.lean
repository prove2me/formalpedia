-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qc_TMat_mul
-- name    : Formalism.InvariantFactorPaths.ColumnFamilies.qc_TMat_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:48:07.49981+00:00
-- url     : https://prove2.me/theorems/3a9e4ee7-783d-4e8a-9bff-0c3c03104b99
-- title:
--   Column Families: qc TMat mul
-- statement:
--   The Column Families construction uses the qc TMat mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/QcEvGLDetUZpow.lean#L163-L172
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/QcEvGLDetUZpow.lean#L163-L172

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_StatementA
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_StatementC
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QcEvGLDetUZpow
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

theorem Formalism.InvariantFactorPaths.ColumnFamilies.qc_TMat_mul {n : ℕ} [NeZero n] (mu : Fin n → ℤ) {R : Type} [CommRing R] (x g : GL (Fin n) R)
    (J I : TIdx mu) :
    evGL (x * g) (TMat mu J I) = ∑ K : TIdx mu, evGL x (TMat mu J K) * evGL g (TMat mu K I) := by sorry
