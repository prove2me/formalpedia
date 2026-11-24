-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qa_minor
-- name    : Formalism.InvariantFactorPaths.ColumnFamilies.qa_minor
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T10:38:44.456873+00:00
-- url     : https://prove2.me/theorems/1ed550af-0cc2-4bce-bacc-02928d9c3faf
-- title:
--   Column Families: qa minor
-- statement:
--   The Column Families construction uses the qa minor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/ABridge.lean#L18-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/ABridge.lean#L18-L25

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QaExpEqBidetExp
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_ABridge
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

theorem Formalism.InvariantFactorPaths.ColumnFamilies.qa_minor (R : Type*) [CommRing R] {n : ℕ} [NeZero n] {mu : Fin n → ℤ} (I : TIdx mu) (c : ↥(TCols mu)) :
    Matrix.det (Matrix.of fun a b : Fin (colH mu c) =>
      genMat R n ((canT mu c).1.orderEmbOfFin (canT mu c).2 a) ((I c).1.orderEmbOfFin (I c).2 b)) =
    rename Prod.swap (initMinor R (qa_row I c) (colH_le mu c)) := by sorry
