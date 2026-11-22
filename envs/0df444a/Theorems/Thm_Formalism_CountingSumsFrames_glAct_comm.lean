-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_glAct_comm
-- name    : Formalism.CountingSumsFrames.glAct_comm
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T21:24:33.617935+00:00
-- url     : https://prove2.me/theorems/bc7e0ae4-6d7c-47f8-9090-2157a30d4ca8
-- title:
--   Counting Sums Frames: gl Act comm
-- statement:
--   The Counting Sums Frames construction uses the gl Act comm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/PartnerM.lean#L1006-L1022
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/PartnerM.lean#L1006-L1022

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

theorem Formalism.CountingSumsFrames.glAct_comm (LL : Letters N) (j : ℕ) (c d a b : Fin r) (x : MvPolynomial (Fin N × Fin r) ℚ_[p]) :
    glAct p LL j c d (glAct p LL j a b x) - glAct p LL j a b (glAct p LL j c d x) =
      (if d = a then glAct p LL j c b x else 0) - (if b = c then glAct p LL j a d x else 0) := by sorry
