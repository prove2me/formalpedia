-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_Har2_levelProj_apply
-- name    : Formalism.CountingSumsFrames.Har2.levelProj_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:34:37.163796+00:00
-- url     : https://prove2.me/theorems/47bcc384-68d3-440d-a146-b13b46e8e955
-- title:
--   Har2: level Proj apply
-- statement:
--   The Har2 construction uses the level Proj apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/HarmonicDecompositionHolds.lean#L487-L491
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/HarmonicDecompositionHolds.lean#L487-L491

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

theorem Formalism.CountingSumsFrames.Har2.levelProj_apply (A B j : ℕ) (f : PolXY K k) : levelProj K k A B j f =
    hXY K k ^ j * (((((A + B + k - 2 * j + j - 1).choose j : ℕ) : K)⁻¹ * ((j.factorial : ℕ) : K)⁻¹) •
      harProj K k (A - j) (B - j) (ctrDiv K k j f)) := by sorry
