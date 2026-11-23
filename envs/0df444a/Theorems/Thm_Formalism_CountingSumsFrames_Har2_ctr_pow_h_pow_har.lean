-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_Har2_ctr_pow_h_pow_har
-- name    : Formalism.CountingSumsFrames.Har2.ctr_pow_h_pow_har
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:34:33.83233+00:00
-- url     : https://prove2.me/theorems/6c803f23-430d-495f-9995-68df74b3fc55
-- title:
--   Har2: ctr pow h pow har
-- statement:
--   The Har2 construction uses the ctr pow h pow har property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/HarmonicDecompositionHolds.lean#L258-L277
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/HarmonicDecompositionHolds.lean#L258-L277

import Definitions.Def_Formalism_PolynomialDimension_StatementHar
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_HarmonicDecompositionHolds
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
open Finset MvPolynomial
open Formalism Formalism.CountingSumsFrames
open Formalism.CountingSumsFrames.Har2
variable {K : Type} [Field K] {k : ℕ}

theorem Formalism.CountingSumsFrames.Har2.ctr_pow_h_pow_har (hk : 1 ≤ k) {a b : ℕ} {w : PolXY K k} (hw : w ∈ HarAB K k a b) (m : ℕ) :
    ∀ i : ℕ, (ctrF K k ^ m) (hXY K k ^ i * w) =
      ((i.descFactorial m * (a + b + k + i - 1).descFactorial m : ℕ) : K) • (hXY K k ^ (i - m) * w) := by sorry
