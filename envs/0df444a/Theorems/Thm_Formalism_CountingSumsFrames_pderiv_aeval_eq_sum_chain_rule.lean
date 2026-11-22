-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_pderiv_aeval_eq_sum_chain_rule
-- name    : Formalism.CountingSumsFrames.pderiv_aeval_eq_sum_chain_rule
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:45:52.208108+00:00
-- url     : https://prove2.me/theorems/a0a29bbe-5bc7-42b6-b6b9-01edc63be0b1
-- title:
--   Counting Sums Frames: pderiv aeval eq sum chain rule
-- statement:
--   The Counting Sums Frames construction uses the pderiv aeval eq sum chain rule property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/DiagLaplacianDivPowMemSqrtFockLattice.lean#L285-L304
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/DiagLaplacianDivPowMemSqrtFockLattice.lean#L285-L304

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

theorem Formalism.CountingSumsFrames.pderiv_aeval_eq_sum_chain_rule {σ : Type} [Fintype σ] (u : σ → MvPolynomial σ K) (v : σ) (f : MvPolynomial σ K) :
    pderiv v (aeval u f) = ∑ w : σ, aeval u (pderiv w f) * pderiv v (u w) := by sorry
