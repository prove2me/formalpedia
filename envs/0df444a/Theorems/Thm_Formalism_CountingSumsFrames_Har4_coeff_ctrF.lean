-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_Har4_coeff_ctrF
-- name    : Formalism.CountingSumsFrames.Har4.coeff_ctrF
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:37:31.910065+00:00
-- url     : https://prove2.me/theorems/908c298a-cd76-43b0-9cb8-594c806277b2
-- title:
--   Har4: coeff ctr F
-- statement:
--   The Har4 construction uses the coeff ctr F property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/SqrtFockGaussLatticeComparisonHolds.lean#L528-L538
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/SqrtFockGaussLatticeComparisonHolds.lean#L528-L538

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
variable {K : Type} [Field K] {k : ℕ}

theorem Formalism.CountingSumsFrames.Har4.coeff_ctrF (f : PolXY K k) (m : XY k →₀ ℕ) :
    coeff m (ctrF K k f) = ∑ i : Fin k,
      coeff (m + Finsupp.single (Sum.inl i) 1 + Finsupp.single (Sum.inr i) 1) f *
        ((m (Sum.inr i) : K) + 1) * ((m (Sum.inl i) : K) + 1) := by sorry
