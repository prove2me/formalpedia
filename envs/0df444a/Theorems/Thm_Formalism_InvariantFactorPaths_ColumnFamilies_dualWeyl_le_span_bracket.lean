-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_dualWeyl_le_span_bracket
-- name    : Formalism.InvariantFactorPaths.ColumnFamilies.dualWeyl_le_span_bracket
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T10:53:48.185295+00:00
-- url     : https://prove2.me/theorems/7fcbae97-4e1f-41f5-a7f5-ec1f2da63e56
-- title:
--   Column Families: dual Weyl le span bracket
-- statement:
--   The Column Families construction uses the dual Weyl le span bracket property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/EvalIdBracketCanonical.lean#L140-L144
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/EvalIdBracketCanonical.lean#L140-L144

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

theorem Formalism.InvariantFactorPaths.ColumnFamilies.dualWeyl_le_span_bracket {n : ℕ} [NeZero n] {mu : Fin n → ℤ} (hmu : Dominant mu) :
    dualWeyl ℤ n n (qn_nu mu) ≤ Submodule.span ℤ (Set.range fun I : TIdx mu => transposeVariables ℤ n (brkPol mu I)) := by sorry
