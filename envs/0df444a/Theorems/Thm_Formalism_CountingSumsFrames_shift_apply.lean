-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_shift_apply
-- name    : Formalism.CountingSumsFrames.shift_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:47:17.172983+00:00
-- url     : https://prove2.me/theorems/cf0e1bfd-b635-4a21-b8ef-0187c51420a1
-- title:
--   Counting Sums Frames: shift apply
-- statement:
--   The Counting Sums Frames construction uses the shift apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/PartnerM.lean#L635-L639
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/PartnerM.lean#L635-L639

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
variable {k σ : Type} [Field k]

theorem Formalism.CountingSumsFrames.shift_apply [DecidableEq σ] (m : σ →₀ ℕ) (u v w : σ) (hv : 1 ≤ m v) :
    ((((Finsupp.single u 1 + (m - Finsupp.single v 1) : σ →₀ ℕ)) w : ℕ) : ℤ) =
      (m w : ℤ) + (if u = w then 1 else 0) - (if v = w then 1 else 0) := by sorry
