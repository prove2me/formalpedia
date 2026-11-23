-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_divPow_mem_of_generators
-- name    : Formalism.CountingSumsFrames.divPow_mem_of_generators
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:43:22.827011+00:00
-- url     : https://prove2.me/theorems/554274dc-507d-47c6-8355-a6b9de77be03
-- title:
--   Counting Sums Frames: div Pow mem of generators
-- statement:
--   The Counting Sums Frames construction uses the div Pow mem of generators property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/DiagLaplacianDivPowMemSqrtFockLattice.lean#L249-L259
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/DiagLaplacianDivPowMemSqrtFockLattice.lean#L249-L259

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
variable {K : Type} [Field K] [CharZero K] {k : ℕ}

theorem Formalism.CountingSumsFrames.divPow_mem_of_generators (L : Set (PolXY K k)) (hadd : ∀ f g, f ∈ L → g ∈ L → f + g ∈ L) (h0 : (0 : PolXY K k) ∈ L)
    (he : ∀ (i : Fin k) (n : ℕ) (f : PolXY K k), f ∈ L → (((n.factorial : K)⁻¹) • h3e K i ^ n) f ∈ L)
    (hd : ∀ (i : Fin k) (n : ℕ) (f : PolXY K k), f ∈ L → (((n.factorial : K)⁻¹) • h3d K i ^ n) f ∈ L)
    (l : ℕ) (f : PolXY K k) (hf : f ∈ L) : hDiv K k l f ∈ L ∧ ctrDiv K k l f ∈ L := by sorry
