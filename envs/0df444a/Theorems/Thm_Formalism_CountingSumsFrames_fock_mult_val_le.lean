-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_fock_mult_val_le
-- name    : Formalism.CountingSumsFrames.fock_mult_val_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:28:12.387191+00:00
-- url     : https://prove2.me/theorems/58d582b6-93d9-4707-9338-45f398ca37cb
-- title:
--   Counting Sums Frames: fock mult val le
-- statement:
--   The Counting Sums Frames construction uses the fock mult val le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/FockGaussComparisonHolds.lean#L22-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/FockGaussComparisonHolds.lean#L22-L25

import Definitions.Def_Formalism_PolynomialDimension_FrameSum
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_FockGaussComparisonHolds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators
open Finset
open Formalism Formalism.CountingSumsFrames

theorem Formalism.CountingSumsFrames.fock_mult_val_le {α : Type*} (p : ℕ) [hp : Fact p.Prime] (f : α → ℕ) (s : Finset α) :
    padicValNat p (Nat.multinomial s f) ≤ s.card * Nat.log p (∑ i ∈ s, f i) := by sorry
