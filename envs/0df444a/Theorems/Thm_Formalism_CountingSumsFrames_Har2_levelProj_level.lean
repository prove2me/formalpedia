-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_Har2_levelProj_level
-- name    : Formalism.CountingSumsFrames.Har2.levelProj_level
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:34:35.214102+00:00
-- url     : https://prove2.me/theorems/2997f237-e607-4d60-951b-1007aa674f17
-- title:
--   Har2: level Proj level
-- statement:
--   The Har2 construction uses the level Proj level property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/HarmonicDecompositionHolds.lean#L505-L538
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/HarmonicDecompositionHolds.lean#L505-L538

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

theorem Formalism.CountingSumsFrames.Har2.levelProj_level [CharZero K] (hk : 1 ≤ k) {A B i j : ℕ} (hi : i ≤ min A B) (hj : j ≤ min A B)
    {w : PolXY K k} (hw : w ∈ HarAB K k (A - i) (B - i)) :
    levelProj K k A B j (hXY K k ^ i * w) = if i = j then hXY K k ^ i * w else 0 := by sorry
