-- Prove2me | Theorems.Thm_Formalism_SA_P_min_one_inv_le
-- name    : Formalism.SA.P.min_one_inv_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:11:11.37947+00:00
-- url     : https://prove2.me/theorems/9fb36a1e-b08c-4de0-8d1e-b062f00f6093
-- title:
--   P: min one inv le
-- statement:
--   The P construction uses the min one inv le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LatticeRigidity/HeightMinimum/SqrtAbsNormLeProd.lean#L232-L245
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LatticeRigidity/HeightMinimum/SqrtAbsNormLeProd.lean#L232-L245

import Definitions.Def_Formalism_LatticeRigidity_StatementC
import Definitions.Def_Formalism_LatticeRigidity_HeightMinimum_SqrtAbsNormLeProd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.SA Formalism.SA.P
open NumberField Finset
variable {E : Type} [Field E] [NumberField E] [NumberField.IsTotallyComplex E]

theorem Formalism.SA.P.min_one_inv_le (u : ℝ) (hu : 0 < u) : min 1 (1 / u) ≤ (1 / 2 : ℝ) ^ (Nat.log 2 ⌊u⌋₊) := by sorry
