-- Prove2me | Theorems.Thm_Formalism_SA_P_min_one_rpow
-- name    : Formalism.SA.P.min_one_rpow
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:11:12.092236+00:00
-- url     : https://prove2.me/theorems/709072e4-e3c0-48eb-bb64-7e1be8dbc761
-- title:
--   P: min one rpow
-- statement:
--   The P construction uses the min one rpow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LatticeRigidity/HeightMinimum/SqrtAbsNormLeProd.lean#L353-L356
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LatticeRigidity/HeightMinimum/SqrtAbsNormLeProd.lean#L353-L356

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

theorem Formalism.SA.P.min_one_rpow (a K : ℝ) (ha : 0 < a) (hK : 0 ≤ K) : min 1 (a ^ K) = (min 1 a) ^ K := by sorry
