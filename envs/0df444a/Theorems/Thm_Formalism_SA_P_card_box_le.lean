-- Prove2me | Theorems.Thm_Formalism_SA_P_card_box_le
-- name    : Formalism.SA.P.card_box_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:11:11.628205+00:00
-- url     : https://prove2.me/theorems/f19e6328-a20e-46e7-9ec4-19a7d3b1493e
-- title:
--   P: card box le
-- statement:
--   The P construction uses the card box le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LatticeRigidity/HeightMinimum/SqrtAbsNormLeProd.lean#L104-L223
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LatticeRigidity/HeightMinimum/SqrtAbsNormLeProd.lean#L104-L223

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

theorem Formalism.SA.P.card_box_le (b : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (hb : b ≠ 0)
    (ρ : InfinitePlace E → ℝ) (hρ : ∀ w, 0 < ρ w) (P : Finset E)
    (hP : ∀ l ∈ P, l ∈ b ∧ l ≠ 0 ∧ ∀ w, w l < ρ w) :
    (P.card : ℝ) ≤ (100 : ℝ) ^ Fintype.card (InfinitePlace E) * (∏ w, ρ w ^ 2) /
      (FractionalIdeal.absNorm b : ℝ) := by sorry
