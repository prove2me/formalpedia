-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qn_T_brkPol
-- name    : Formalism.InvariantFactorPaths.ColumnFamilies.qn_T_brkPol
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T10:52:54.784801+00:00
-- url     : https://prove2.me/theorems/21cb7346-a1d1-431e-9592-e74e5c59f51a
-- title:
--   Column Families: qn T brk Pol
-- statement:
--   The Column Families construction uses the qn T brk Pol property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/EvalIdBracketCanonical.lean#L123-L127
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/EvalIdBracketCanonical.lean#L123-L127

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_TransposeVariables
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_ABridge
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_BideterminantMem
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LHwrowLemmas
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_EvalIdBracketCanonical
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.ColumnFamilies
open Formalism.GradedWeylDivisibility

theorem Formalism.InvariantFactorPaths.ColumnFamilies.qn_T_brkPol {n : ℕ} [NeZero n] (mu : Fin n → ℤ) (I : TIdx mu) :
    transposeVariables ℤ n (brkPol mu I) = qn_delta n ^ (mu (lastIdx n)).toNat * qa_P ℤ I := by sorry
