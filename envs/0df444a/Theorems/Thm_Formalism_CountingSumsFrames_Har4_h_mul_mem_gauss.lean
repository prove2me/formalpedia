-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_Har4_h_mul_mem_gauss
-- name    : Formalism.CountingSumsFrames.Har4.h_mul_mem_gauss
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:38:06.4298+00:00
-- url     : https://prove2.me/theorems/323f49ac-e029-46ad-8bb9-9c2513cc94a3
-- title:
--   Har4: h mul mem gauss
-- statement:
--   The Har4 construction uses the h mul mem gauss property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/SqrtFockGaussLatticeComparisonHolds.lean#L453-L464
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/SqrtFockGaussLatticeComparisonHolds.lean#L453-L464

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

theorem Formalism.CountingSumsFrames.Har4.h_mul_mem_gauss {K : Type} [Field K] {k : ℕ} (R : Subring K) (G : PolXY K k) (hG : G ∈ GaussLat R) :
    hXY K k * G ∈ GaussLat R := by sorry
