-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_Har4_sqrtFock_to_sqrtGauss
-- name    : Formalism.CountingSumsFrames.Har4.sqrtFock_to_sqrtGauss
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:38:20.669441+00:00
-- url     : https://prove2.me/theorems/8c642f24-551e-4243-afc1-56d9bebb593a
-- title:
--   Har4: sqrt Fock to sqrt Gauss
-- statement:
--   The Har4 construction uses the sqrt Fock to sqrt Gauss property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/SqrtFockGaussLatticeComparisonHolds.lean#L368-L381
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/SqrtFockGaussLatticeComparisonHolds.lean#L368-L381

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

theorem Formalism.CountingSumsFrames.Har4.sqrtFock_to_sqrtGauss {f : PolXY K k} (hf : f ∈ PolAB K k A B) (h : f ∈ SqrtFockLat R) :
    f ∈ SqrtGaussLat R (A.factorial * B.factorial) := by sorry
