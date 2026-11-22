-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_Har2_lin_mem
-- name    : Formalism.CountingSumsFrames.Har2.lin_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:15:11.585489+00:00
-- url     : https://prove2.me/theorems/f745e3d2-0d90-4f1e-b772-41742ecafe47
-- title:
--   Har2: lin mem
-- statement:
--   The Har2 construction uses the lin mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/HarmonicDecompositionHolds.lean#L22-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/HarmonicDecompositionHolds.lean#L22-L27

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

theorem Formalism.CountingSumsFrames.Har2.lin_mem {A B : ℕ} (T : PolXY K k →ₗ[K] PolXY K k) (S : Submodule K (PolXY K k))
    (h : ∀ (m : XY k →₀ ℕ) (c : K), xDeg m = A → yDeg m = B → T (monomial m c) ∈ S)
    {f : PolXY K k} (hf : f ∈ PolAB K k A B) : T f ∈ S := by sorry
