-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qc_cb_minor
-- name    : Formalism.InvariantFactorPaths.ColumnFamilies.qc_cb_minor
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:18:52.051016+00:00
-- url     : https://prove2.me/theorems/fb63e6ea-9658-4a72-a06e-5a5e2129b08e
-- title:
--   Column Families: qc cb minor
-- statement:
--   The Column Families construction uses the qc cb minor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/QcEvGLDetUZpow.lean#L122-L128
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/QcEvGLDetUZpow.lean#L122-L128

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

theorem Formalism.InvariantFactorPaths.ColumnFamilies.qc_cb_minor {R : Type} [CommRing R] {n h : ℕ} (x g : Matrix (Fin n) (Fin n) R) (r c : Fin h → Fin n) :
    ((x * g).submatrix r c).det = ∑ S : {S : Finset (Fin n) // S.card = h},
      (x.submatrix r (S.1.orderEmbOfFin S.2)).det * (g.submatrix (S.1.orderEmbOfFin S.2) c).det := by sorry
