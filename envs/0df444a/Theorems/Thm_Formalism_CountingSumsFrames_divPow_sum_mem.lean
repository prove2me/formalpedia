-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_divPow_sum_mem
-- name    : Formalism.CountingSumsFrames.divPow_sum_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:43:22.448317+00:00
-- url     : https://prove2.me/theorems/5be4daff-d610-4baa-a15b-228fc58d251e
-- title:
--   Counting Sums Frames: div Pow sum mem
-- statement:
--   The Counting Sums Frames construction uses the div Pow sum mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/DiagLaplacianDivPowMemSqrtFockLattice.lean#L38-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/DiagLaplacianDivPowMemSqrtFockLattice.lean#L38-L51

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

theorem Formalism.CountingSumsFrames.divPow_sum_mem {ι : Type*} (S : Subsemiring E) (s : Finset ι) (a : ι → E)
    (hc : ∀ i j, Commute (a i) (a j)) (ha : ∀ (i : ι) (n : ℕ), ((n.factorial : K)⁻¹) • a i ^ n ∈ S) :
    ∀ n : ℕ, ((n.factorial : K)⁻¹) • (∑ i ∈ s, a i) ^ n ∈ S := by sorry
