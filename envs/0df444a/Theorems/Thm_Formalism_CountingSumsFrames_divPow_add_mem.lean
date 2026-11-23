-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_divPow_add_mem
-- name    : Formalism.CountingSumsFrames.divPow_add_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:43:22.988804+00:00
-- url     : https://prove2.me/theorems/913c02fe-b8ad-4835-91d0-c5b7cb93c527
-- title:
--   Counting Sums Frames: div Pow add mem
-- statement:
--   The Counting Sums Frames construction uses the div Pow add mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/DiagLaplacianDivPowMemSqrtFockLattice.lean#L14-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/DiagLaplacianDivPowMemSqrtFockLattice.lean#L14-L36

import Definitions.Def_Formalism_PolynomialDimension_StatementHar
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_DiagLaplacianDivPowMemSqrtFockLattice
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
variable {K E : Type*} [Field K] [CharZero K] [Ring E] [Algebra K E]

theorem Formalism.CountingSumsFrames.divPow_add_mem (S : Subsemiring E) (a b : E) (hab : Commute a b)
    (ha : ∀ n : ℕ, ((n.factorial : K)⁻¹) • a ^ n ∈ S) (hb : ∀ n : ℕ, ((n.factorial : K)⁻¹) • b ^ n ∈ S)
    (n : ℕ) : ((n.factorial : K)⁻¹) • (a + b) ^ n ∈ S := by sorry
