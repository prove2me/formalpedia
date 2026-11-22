-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_vdm
-- name    : Formalism.CountingSumsFrames.vdm
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:47:17.1715+00:00
-- url     : https://prove2.me/theorems/18cd5c27-7559-474b-8d65-67503c4fc90f
-- title:
--   Counting Sums Frames: vdm
-- statement:
--   The Counting Sums Frames construction uses the vdm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/PartnerM.lean#L1319-L1396
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/PartnerM.lean#L1319-L1396

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
variable {K σ : Type} [Field K]

theorem Formalism.CountingSumsFrames.vdm (H : MvPolynomial σ K →ₗ[K] MvPolynomial σ K) (f : (σ →₀ ℕ) → ℤ) [CharZero K]
    (hH : ∀ x m, coeff m (H x) = ((f m : ℤ) : K) * coeff m x) (S : Submodule K (MvPolynomial σ K))
    (hS : ∀ x ∈ S, H x ∈ S) : ∀ x ∈ S, ∀ k : ℤ, compP (fun m => f m = k) x ∈ S := by sorry
