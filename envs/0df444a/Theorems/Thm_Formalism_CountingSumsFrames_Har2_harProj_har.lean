-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_Har2_harProj_har
-- name    : Formalism.CountingSumsFrames.Har2.harProj_har
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:34:32.149427+00:00
-- url     : https://prove2.me/theorems/17ae0edf-0f82-4bb6-b0c9-5707e2e34004
-- title:
--   Har2: har Proj har
-- statement:
--   The Har2 construction uses the har Proj har property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/HarmonicDecompositionHolds.lean#L391-L396
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/HarmonicDecompositionHolds.lean#L391-L396

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

theorem Formalism.CountingSumsFrames.Har2.harProj_har {A B : ℕ} {f : PolXY K k} (hf : f ∈ HarAB K k A B) : harProj K k A B f = f := by sorry
