-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_ops_keep_supp
-- name    : Formalism.CountingSumsFrames.ops_keep_supp
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:27:04.329953+00:00
-- url     : https://prove2.me/theorems/7dcba474-9680-4703-b532-040f3902e69b
-- title:
--   Counting Sums Frames: ops keep supp
-- statement:
--   The Counting Sums Frames construction uses the ops keep supp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/PartnerM.lean#L227-L268
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/PartnerM.lean#L227-L268

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

theorem Formalism.CountingSumsFrames.ops_keep_supp (S : Set σ) (Q : Set (σ →₀ ℕ))
    (hQ : ∀ m m' : σ →₀ ℕ, (∀ v, v ∉ S → m v = m' v) → m ∈ Q → m' ∈ Q)
    {T : Module.End k (MvPolynomial σ k)} (hT : T ∈ FockB.Ops S) :
    ∀ x ∈ restrictSupport k Q, T x ∈ restrictSupport k Q := by sorry
