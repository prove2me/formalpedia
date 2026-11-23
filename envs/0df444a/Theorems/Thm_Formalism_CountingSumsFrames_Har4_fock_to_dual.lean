-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_Har4_fock_to_dual
-- name    : Formalism.CountingSumsFrames.Har4.fock_to_dual
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:37:52.345661+00:00
-- url     : https://prove2.me/theorems/4568bd44-37bc-4927-a3f3-65d94c016d4d
-- title:
--   Har4: fock to dual
-- statement:
--   The Har4 construction uses the fock to dual property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/SqrtFockGaussLatticeComparisonHolds.lean#L346-L366
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/SqrtFockGaussLatticeComparisonHolds.lean#L346-L366

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
variable {K : Type} [Field K] [CharZero K] {k A B : ℕ} (R : Subring K)

theorem Formalism.CountingSumsFrames.Har4.fock_to_dual {p : ℕ} (hp : p.Prime) (hR : PLocal R p) {f : PolXY K k} (hf : f ∈ PolAB K k A B)
    (h : f ∈ FockLat R) :
    ((p : K) ^ ((k - 1) * Nat.log p B) * (B.factorial : K)⁻¹) • f ∈ DualLat R := by sorry
