-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_Har4_gauss_dual_of_fock
-- name    : Formalism.CountingSumsFrames.Har4.gauss_dual_of_fock
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T10:38:00.226845+00:00
-- url     : https://prove2.me/theorems/dd013914-c831-4061-a533-7a78d27642c0
-- title:
--   Har4: gauss dual of fock
-- statement:
--   The Har4 construction uses the gauss dual of fock property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/SqrtFockGaussLatticeComparisonHolds.lean#L647-L707
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/SqrtFockGaussLatticeComparisonHolds.lean#L647-L707

import Definitions.Def_Formalism_PolynomialDimension_StatementHar
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_HarmonicDecompositionHolds
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_DiagLaplacianDivPowMemSqrtFockLattice
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_SqrtFockGaussLatticeComparisonHolds
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
open Formalism.CountingSumsFrames.Har4

theorem Formalism.CountingSumsFrames.Har4.gauss_dual_of_fock {K : Type} [Field K] [CharZero K] {k A B p : ℕ} (R : Subring K) (g : GL (Fin k) K)
    (hk : 1 ≤ k) (hp : p.Prime) (hR : PLocal R p) (T : PolXY K k →ₗ[K] PolXY K k)
    (hT : ∀ f, f ∈ PolAB K k A B → T f ∈ PolAB K k A B) (n : ℕ) (hn : n ≤ 2 * Nat.log p (A + B + k))
    (hF : ∀ f, f ∈ PolAB K k A B → f ∈ latOf g (FockLat R) → ((p : K) ^ n) • T f ∈ latOf g (FockLat R))
    (f : PolXY K k) (hf : f ∈ PolAB K k A B) :
    (f ∈ latOf g (GaussLat R) → ((p : K) ^ ((k + 1) * Nat.log p (A + B + k))) • T f ∈ latOf g (GaussLat R)) ∧
    (f ∈ latOf g (DualLat R) → ((p : K) ^ ((k + 1) * Nat.log p (A + B + k))) • T f ∈ latOf g (DualLat R)) := by sorry
