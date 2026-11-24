-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_dualWeyl_eq_span_tableauBideterminant
-- name    : Formalism.InvariantFactorPaths.ColumnFamilies.dualWeyl_eq_span_tableauBideterminant
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T10:25:58.754178+00:00
-- url     : https://prove2.me/theorems/08f84b11-9494-4d04-b87d-b19f5bb634fe
-- title:
--   Column Families: dual Weyl eq span tableau Bideterminant
-- statement:
--   The Column Families construction uses the dual Weyl eq span tableau Bideterminant property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/QaExpEqBidetExp.lean#L158-L168
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/QaExpEqBidetExp.lean#L158-L168

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QaNuAntitone
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QaExpEqBidetExp
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

theorem Formalism.InvariantFactorPaths.ColumnFamilies.dualWeyl_eq_span_tableauBideterminant (B : Type) [CommRing B] [IsDomain B] {n : ℕ} [NeZero n] {mu : Fin n → ℤ}
    (hmu : Dominant mu) :
    dualWeyl B n n (qa_nu mu) = Submodule.span B (Set.range fun I : TIdx mu => qa_P B I) := by sorry
