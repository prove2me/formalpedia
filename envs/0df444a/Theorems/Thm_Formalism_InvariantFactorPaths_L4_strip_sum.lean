-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_L4_strip_sum
-- name    : Formalism.InvariantFactorPaths.L4.strip_sum
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:42:14.826339+00:00
-- url     : https://prove2.me/theorems/58d036fa-4c4f-477b-821e-befd2c1e0d50
-- title:
--   L4: strip sum
-- statement:
--   The L4 construction uses the strip sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/Vanish.lean#L30-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/Vanish.lean#L30-L40

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementG
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_OmegaInjectiveHolds
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_Vanish
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.L4
open Formalism.GM Formalism.GM.M Formalism.GM.TM Formalism.GM.MeanGammaLemmas Formalism.CountingSumsFrames MvPolynomial Finset

theorem Formalism.InvariantFactorPaths.L4.strip_sum (t b : ℕ → ℤ) (n : ℕ) (h : ∀ i, i + 1 < n → t (i + 1) ≤ t i - b i) :
    ∀ k, k < n → ∑ i ∈ range (k + 1), b i ≤ t 0 - (t k - b k) := by sorry
