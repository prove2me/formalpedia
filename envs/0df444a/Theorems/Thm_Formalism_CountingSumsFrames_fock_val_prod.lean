-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_fock_val_prod
-- name    : Formalism.CountingSumsFrames.fock_val_prod
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:39:24.042297+00:00
-- url     : https://prove2.me/theorems/91964b16-3e1d-4519-a393-20b0af543b12
-- title:
--   Counting Sums Frames: fock val prod
-- statement:
--   The Counting Sums Frames construction uses the fock val prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/FockGaussComparisonHolds.lean#L27-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/FockGaussComparisonHolds.lean#L27-L38

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

theorem Formalism.CountingSumsFrames.fock_val_prod {ι : Type*} (p : ℕ) [Fact p.Prime] (s : Finset ι) (f : ι → ℕ)
    (hf : ∀ i ∈ s, f i ≠ 0) :
    padicValNat p (∏ i ∈ s, f i) = ∑ i ∈ s, padicValNat p (f i) := by sorry
