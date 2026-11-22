-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_glAct_eq_sum
-- name    : Formalism.CountingSumsFrames.glAct_eq_sum
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:41:30.776478+00:00
-- url     : https://prove2.me/theorems/69748209-f9a1-4b21-a3c9-7439a41f771c
-- title:
--   Counting Sums Frames: gl Act eq sum
-- statement:
--   The Counting Sums Frames construction uses the gl Act eq sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/PartnerM.lean#L923-L924
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/PartnerM.lean#L923-L924

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

theorem Formalism.CountingSumsFrames.glAct_eq_sum (LL : Letters N) (j : ℕ) (c d : Fin r) :
    glAct p LL j c d = ∑ i : Fin N, tm (p := p) LL j i c d := by sorry
