-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qa_cum
-- name    : Formalism.InvariantFactorPaths.ColumnFamilies.qa_cum
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:48:21.541487+00:00
-- url     : https://prove2.me/theorems/af3fb09b-0d2f-4ad9-8ef0-d09665667423
-- title:
--   Column Families: qa cum
-- statement:
--   The Column Families construction uses the qa cum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/QaRowStrictMono.lean#L97-L131
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/QaRowStrictMono.lean#L97-L131

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DefsMod
import Definitions.Def_Formalism_GradedWeylDivisibility_StatementD
import Definitions.Def_Lemmata_GeneralBFactSecondTer_Imports
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QaRowStrictMono
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

theorem Formalism.InvariantFactorPaths.ColumnFamilies.qa_cum {n : ℕ} [NeZero n] {mu : Fin n → ℤ} (I : TIdx mu) (a p : Fin n) :
    ∑ b : Fin n with b ≤ a, qa_exp I (b, p) =
      (univ.filter fun c : ↥(TCols mu) => p.val < qa_cnt I c a).card := by sorry
