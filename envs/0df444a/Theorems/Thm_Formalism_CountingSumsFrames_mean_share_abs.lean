-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_mean_share_abs
-- name    : Formalism.CountingSumsFrames.mean_share_abs
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T13:48:13.22698+00:00
-- url     : https://prove2.me/theorems/1aad789c-d105-4d2b-ae73-92fd60effdb9
-- title:
--   Counting Sums Frames: mean share abs
-- statement:
--   The Counting Sums Frames construction uses the mean share abs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/SegmentBoundThreeHolds.lean#L265-L339
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/SegmentBoundThreeHolds.lean#L265-L339

import Definitions.Def_Formalism_PolynomialDimension_DigitSumValuationBound
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_SegmentBoundThreeHolds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset
open Formalism Formalism.CountingSumsFrames

theorem Formalism.CountingSumsFrames.mean_share_abs {α β R : Type} [Fintype β] [Fintype R] (W : Finset α) (compat : β → α → Prop)
    [∀ ρ aa, Decidable (compat ρ aa)] (ny : ℕ) (hny : 0 < ny)
    (hcount : ∀ aa ∈ W, ((univ : Finset β).filter (fun ρ => compat ρ aa)).card = ny)
    (bad rk : β → R → α → ℝ) (Mlo Mhi : R → ℝ) (eps K : ℝ) (hW : W.Nonempty) (heps : 0 ≤ eps) (hK : 0 ≤ K)
    (hbad : ∀ ρ q aa, 0 ≤ bad ρ q aa) (hMlo : ∀ q, 0 ≤ Mlo q) (hMhi : ∀ q, Mhi q ≤ K * Mlo q)
    (hrk : ∀ ρ q, ∀ aa ∈ W, compat ρ aa → Mlo q / 2 ≤ rk ρ q aa)
    (hsum : ∀ ρ q, ∑ aa ∈ W.filter (fun aa => compat ρ aa), bad ρ q aa ≤
      eps * ((W.filter (fun aa => compat ρ aa)).card : ℝ) * Mhi q) :
    (∑ aa ∈ W, (∑ ρ ∈ univ.filter (fun ρ : β => compat ρ aa), ∑ q, bad ρ q aa) /
      (∑ ρ ∈ univ.filter (fun ρ : β => compat ρ aa), ∑ q, rk ρ q aa)) / (W.card : ℝ) ≤ 2 * K * eps := by sorry
