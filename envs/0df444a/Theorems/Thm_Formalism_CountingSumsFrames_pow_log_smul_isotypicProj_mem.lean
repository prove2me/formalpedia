-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_pow_log_smul_isotypicProj_mem
-- name    : Formalism.CountingSumsFrames.pow_log_smul_isotypicProj_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:50:57.826263+00:00
-- url     : https://prove2.me/theorems/d9826074-7ad6-4050-b848-5eed8e2c8ef3
-- title:
--   Counting Sums Frames: pow log smul isotypic Proj mem
-- statement:
--   The Counting Sums Frames construction uses the pow log smul isotypic Proj mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/DiagLaplacianDivPowMemSqrtFockLattice.lean#L411-L430
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/DiagLaplacianDivPowMemSqrtFockLattice.lean#L411-L430

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

theorem Formalism.CountingSumsFrames.pow_log_smul_isotypicProj_mem (R : Subring K) (p : ℕ) (hp : p.Prime) (hR : PLocal R p) (M : Set (PolXY K k))
    (h0 : (0 : PolXY K k) ∈ M) (hadd : ∀ f g, f ∈ M → g ∈ M → f + g ∈ M)
    (hs : ∀ r ∈ R, ∀ f ∈ M, r • f ∈ M)
    (hM : ∀ (l : ℕ) (f : PolXY K k), f ∈ M → hDiv K k l f ∈ M ∧ ctrDiv K k l f ∈ M)
    (A B j : ℕ) (hj : j ≤ A) (f : PolXY K k) (hf : f ∈ M) :
    ((p : K) ^ (2 * Nat.log p (A + B + k))) • levelProj K k A B j f ∈ M := by sorry
