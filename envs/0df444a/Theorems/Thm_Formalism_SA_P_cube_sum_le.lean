-- Prove2me | Theorems.Thm_Formalism_SA_P_cube_sum_le
-- name    : Formalism.SA.P.cube_sum_le
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T10:27:26.517923+00:00
-- url     : https://prove2.me/theorems/063dbf10-6322-4d17-90d2-af7cdd3dc4fe
-- title:
--   P: cube sum le
-- statement:
--   The P construction uses the cube sum le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LatticeRigidity/HeightMinimum/SqrtAbsNormLeProd.lean#L271-L351
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LatticeRigidity/HeightMinimum/SqrtAbsNormLeProd.lean#L271-L351

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

theorem Formalism.SA.P.cube_sum_le (b : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (hb : b ≠ 0)
    (x : InfinitePlace E → ℝ) (hx : ∀ w, 0 < x w) (S : Finset E) (hS : ∀ l ∈ S, l ∈ b ∧ l ≠ 0) :
    ∑ l ∈ S, (∏ w, min 1 (x w / w l)) ^ 3 ≤
      (800 : ℝ) ^ Fintype.card (InfinitePlace E) * (∏ w, x w) ^ 2 /
        (FractionalIdeal.absNorm b : ℝ) := by sorry
