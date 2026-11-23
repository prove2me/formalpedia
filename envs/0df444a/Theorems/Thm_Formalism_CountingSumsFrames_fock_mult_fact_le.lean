-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_fock_mult_fact_le
-- name    : Formalism.CountingSumsFrames.fock_mult_fact_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:46:36.276265+00:00
-- url     : https://prove2.me/theorems/e147862c-eb84-48d1-8fdb-901bc2afb600
-- title:
--   Counting Sums Frames: fock mult fact le
-- statement:
--   The Counting Sums Frames construction uses the fock mult fact le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/FockGaussComparisonHolds.lean#L8-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/FockGaussComparisonHolds.lean#L8-L20

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

theorem Formalism.CountingSumsFrames.fock_mult_fact_le {α : Type*} (p : ℕ) (f : α → ℕ) (s : Finset α) :
    (Nat.multinomial s f).factorization p ≤ s.card * Nat.log p (∑ i ∈ s, f i) := by sorry
