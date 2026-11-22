-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_XD_keep
-- name    : Formalism.CountingSumsFrames.XD_keep
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:41:23.678339+00:00
-- url     : https://prove2.me/theorems/725196ad-6286-4529-b878-0b818a76e4e1
-- title:
--   Counting Sums Frames: XD keep
-- statement:
--   The Counting Sums Frames construction uses the XD keep property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/PartnerM.lean#L618-L633
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/PartnerM.lean#L618-L633

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

theorem Formalism.CountingSumsFrames.XD_keep (u v : σ) (Q Q' : Set (σ →₀ ℕ))
    (h : ∀ m ∈ Q, 1 ≤ m v → Finsupp.single u 1 + (m - Finsupp.single v 1) ∈ Q') :
    ∀ x ∈ restrictSupport k Q, X u * pderiv v x ∈ restrictSupport k Q' := by sorry
