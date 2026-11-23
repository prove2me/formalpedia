-- Prove2me | Theorems.Thm_Formalism_SA_P_sqrt_absNorm_le_prod
-- name    : Formalism.SA.P.sqrt_absNorm_le_prod
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T05:11:40.498916+00:00
-- url     : https://prove2.me/theorems/011d2410-8075-4a80-b55e-32345014c33d
-- title:
--   P: sqrt abs Norm le prod
-- statement:
--   The P construction uses the sqrt abs Norm le prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LatticeRigidity/HeightMinimum/SqrtAbsNormLeProd.lean#L47-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LatticeRigidity/HeightMinimum/SqrtAbsNormLeProd.lean#L47-L61

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

theorem Formalism.SA.P.sqrt_absNorm_le_prod (b : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (hb : b ≠ 0)
    (l : E) (hl : l ∈ b) (hl0 : l ≠ 0) :
    √(FractionalIdeal.absNorm b : ℝ) ≤ ∏ w : InfinitePlace E, w l := by sorry
