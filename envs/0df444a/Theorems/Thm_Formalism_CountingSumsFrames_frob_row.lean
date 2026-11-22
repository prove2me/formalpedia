-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_frob_row
-- name    : Formalism.CountingSumsFrames.frob_row
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:41:31.468419+00:00
-- url     : https://prove2.me/theorems/9cccb6bd-eefb-4149-893c-ddcbd824af6f
-- title:
--   Counting Sums Frames: frob row
-- statement:
--   The Counting Sums Frames construction uses the frob row property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/FrobeniusDetVanishingHolds.lean#L49-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/FrobeniusDetVanishingHolds.lean#L49-L57

import Definitions.Def_Formalism_PolynomialDimension_FrameSum
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_FrobeniusDetVanishingHolds
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
open Finset Matrix
open Formalism Formalism.CountingSumsFrames

theorem Formalism.CountingSumsFrames.frob_row {p : ℕ} [Fact p.Prime] {F : Type} [Field F] [CharP F p] {k : ℕ}
    (h : Matrix (Fin k) (Fin k) F) (a s : ℕ) (ha : a ≤ s) (t : Fin k → F) (c : Fin k) :
    ((t ᵥ* h.map (fun x => x ^ p ^ a)) c) ^ p ^ (s - a) =
      ((fun i => t i ^ p ^ (s - a)) ᵥ* h.map (fun x => x ^ p ^ s)) c := by sorry
