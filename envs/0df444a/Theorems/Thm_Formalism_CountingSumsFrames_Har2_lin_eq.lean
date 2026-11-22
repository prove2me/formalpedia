-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_Har2_lin_eq
-- name    : Formalism.CountingSumsFrames.Har2.lin_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:34:43.920139+00:00
-- url     : https://prove2.me/theorems/1d7ff62a-7779-4e3f-b0d9-c803173e385a
-- title:
--   Har2: lin eq
-- statement:
--   The Har2 construction uses the lin eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/HarmonicDecompositionHolds.lean#L29-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/HarmonicDecompositionHolds.lean#L29-L34

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

theorem Formalism.CountingSumsFrames.Har2.lin_eq {A B : ℕ} (T T' : PolXY K k →ₗ[K] PolXY K k)
    (h : ∀ (m : XY k →₀ ℕ) (c : K), xDeg m = A → yDeg m = B → T (monomial m c) = T' (monomial m c))
    {f : PolXY K k} (hf : f ∈ PolAB K k A B) : T f = T' f := by sorry
