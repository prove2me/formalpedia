-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qa_std_iff
-- name    : Formalism.InvariantFactorPaths.ColumnFamilies.qa_std_iff
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:26:14.359802+00:00
-- url     : https://prove2.me/theorems/0324d9d6-3292-4b7d-8fec-609f74886b38
-- title:
--   Column Families: qa std iff
-- statement:
--   The Column Families construction uses the qa std iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/QaRowStrictMono.lean#L145-L157
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/QaRowStrictMono.lean#L145-L157

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

theorem Formalism.InvariantFactorPaths.ColumnFamilies.qa_std_iff {n : ℕ} [NeZero n] {mu : Fin n → ℤ} (I : TIdx mu) (hI : StdT I) (c : ↥(TCols mu))
    (a p : Fin n) :
    p.val < qa_cnt I c a ↔
      (c : ℤ) - mu (lastIdx n) ≤ ((∑ b : Fin n with b ≤ a, qa_exp I (b, p) : ℕ) : ℤ) := by sorry
