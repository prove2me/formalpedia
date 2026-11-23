-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_glAct_wtsp
-- name    : Formalism.CountingSumsFrames.glAct_wtsp
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T13:47:02.339572+00:00
-- url     : https://prove2.me/theorems/2aa9cfae-a1cc-4cba-803a-9026cadf7268
-- title:
--   Counting Sums Frames: gl Act wtsp
-- statement:
--   The Counting Sums Frames construction uses the gl Act wtsp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/PartnerM.lean#L842-L855
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/PartnerM.lean#L842-L855

import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_TheoremM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FockBlocks
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_RemoveS
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_PartnerM
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.CountingSumsFrames
open Formalism.GM Formalism.GM.TM M MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}

theorem Formalism.CountingSumsFrames.glAct_wtsp (LL : Letters N) (j : ℕ) (c d : Fin r) (μ : Fin r → ℤ) :
    ∀ x ∈ WtSpC p LL j univ μ, glAct p LL j c d x ∈ WtSpC p LL j univ (shiftW μ c d) := by sorry
