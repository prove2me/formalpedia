-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_pow_log_smul_harmonicProj_mem
-- name    : Formalism.CountingSumsFrames.pow_log_smul_harmonicProj_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:46:42.225337+00:00
-- url     : https://prove2.me/theorems/73f319a0-c2da-410f-97d1-34ac93e69d46
-- title:
--   Counting Sums Frames: pow log smul harmonic Proj mem
-- statement:
--   The Counting Sums Frames construction uses the pow log smul harmonic Proj mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/DiagLaplacianDivPowMemSqrtFockLattice.lean#L387-L409
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/DiagLaplacianDivPowMemSqrtFockLattice.lean#L387-L409

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

theorem Formalism.CountingSumsFrames.pow_log_smul_harmonicProj_mem (R : Subring K) (p : ℕ) (hp : p.Prime) (hR : PLocal R p) (M : Set (PolXY K k))
    (h0 : (0 : PolXY K k) ∈ M) (hadd : ∀ f g, f ∈ M → g ∈ M → f + g ∈ M)
    (hs : ∀ r ∈ R, ∀ f ∈ M, r • f ∈ M)
    (hM : ∀ (l : ℕ) (f : PolXY K k), f ∈ M → hDiv K k l f ∈ M ∧ ctrDiv K k l f ∈ M)
    (a b N : ℕ) (hN : a + b + k ≤ N) (f : PolXY K k) (hf : f ∈ M) :
    ((p : K) ^ Nat.log p N) • harProj K k a b f ∈ M := by sorry
