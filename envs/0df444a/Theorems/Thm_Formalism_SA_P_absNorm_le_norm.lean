-- Prove2me | Theorems.Thm_Formalism_SA_P_absNorm_le_norm
-- name    : Formalism.SA.P.absNorm_le_norm
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T10:27:16.655243+00:00
-- url     : https://prove2.me/theorems/ab3125d3-d525-4e93-a2ee-84d99238e92f
-- title:
--   P: abs Norm le norm
-- statement:
--   The P construction uses the abs Norm le norm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LatticeRigidity/HeightMinimum/SqrtAbsNormLeProd.lean#L7-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LatticeRigidity/HeightMinimum/SqrtAbsNormLeProd.lean#L7-L43

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

theorem Formalism.SA.P.absNorm_le_norm {E : Type} [Field E] [NumberField E]
    (b : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (hb : b ≠ 0) (l : E) (hl : l ∈ b) (hl0 : l ≠ 0) :
    (FractionalIdeal.absNorm b : ℝ) ≤ |(Algebra.norm ℚ l : ℝ)| := by sorry
