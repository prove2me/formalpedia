-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qc_evGL_minorC
-- name    : Formalism.InvariantFactorPaths.ColumnFamilies.qc_evGL_minorC
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:37:28.461072+00:00
-- url     : https://prove2.me/theorems/dcf4c477-ed89-4995-bf44-59b5b3a23cd2
-- title:
--   Column Families: qc ev GL minor C
-- statement:
--   The Column Families construction uses the qc ev GL minor C property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/QcEvGLDetUZpow.lean#L135-L141
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/QcEvGLDetUZpow.lean#L135-L141

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

theorem Formalism.InvariantFactorPaths.ColumnFamilies.qc_evGL_minorC {n h : ℕ} {R : Type} [CommRing R] (g : GL (Fin n) R) (J I : Finset (Fin n))
    (hJ : J.card = h) (hI : I.card = h) :
    evGL g (minorC J I hJ hI) = (g.val.submatrix (J.orderEmbOfFin hJ) (I.orderEmbOfFin hI)).det := by sorry
