-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qn_mem_weightSp
-- name    : Formalism.InvariantFactorPaths.ColumnFamilies.qn_mem_weightSp
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:18:32.400769+00:00
-- url     : https://prove2.me/theorems/bab4db7d-d9cd-4938-8c3f-a3c72998fa1a
-- title:
--   Column Families: qn mem weight Sp
-- statement:
--   The Column Families construction uses the qn mem weight Sp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/CoeffTransposeVariables.lean#L39-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/CoeffTransposeVariables.lean#L39-L43

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_TransposeVariables
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_FockQHW
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_CoeffTransposeVariables
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

theorem Formalism.InvariantFactorPaths.ColumnFamilies.qn_mem_weightSp (n : ℕ) (w : Fin n → ℤ) (z : MvPolynomial (Fin n × Fin n) ℚ) :
    z ∈ weightSp (glOps ℚ n (rowLetters n) Set.univ) w ↔
      ∀ a, glOps ℚ n (rowLetters n) Set.univ a a z = (w a : ℚ) • z := by sorry
