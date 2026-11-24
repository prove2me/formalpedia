-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qc_evGL_detU
-- name    : Formalism.InvariantFactorPaths.ColumnFamilies.qc_evGL_detU
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:21:05.850821+00:00
-- url     : https://prove2.me/theorems/2ff8f758-ea86-4c37-8273-71a6489d50f2
-- title:
--   Column Families: qc ev GL det U
-- statement:
--   The Column Families construction uses the qc ev GL det U property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/QcEvGLDetUZpow.lean#L145-L147
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/QcEvGLDetUZpow.lean#L145-L147

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

theorem Formalism.InvariantFactorPaths.ColumnFamilies.qc_evGL_detU {n : ℕ} {R : Type} [CommRing R] (g : GL (Fin n) R) :
    evGL g ((detU n : (GLCoord ℤ n)ˣ) : GLCoord ℤ n) = g.val.det := by sorry
