-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_Har4_sqrtGauss_to_sqrtFock
-- name    : Formalism.CountingSumsFrames.Har4.sqrtGauss_to_sqrtFock
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:41:31.353101+00:00
-- url     : https://prove2.me/theorems/90658180-c278-4f4a-87e7-c75593dcb79b
-- title:
--   Har4: sqrt Gauss to sqrt Fock
-- statement:
--   The Har4 construction uses the sqrt Gauss to sqrt Fock property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/SqrtFockGaussLatticeComparisonHolds.lean#L383-L410
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/SqrtFockGaussLatticeComparisonHolds.lean#L383-L410

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

theorem Formalism.CountingSumsFrames.Har4.sqrtGauss_to_sqrtFock {p : ℕ} (hp : p.Prime) (hR : PLocal R p) {f : PolXY K k}
    (hf : f ∈ PolAB K k A B) (h : f ∈ SqrtGaussLat R (A.factorial * B.factorial)) :
    ((p : K) ^ ((k - 1) * Nat.log p (A + B + k))) • f ∈ SqrtFockLat R := by sorry
