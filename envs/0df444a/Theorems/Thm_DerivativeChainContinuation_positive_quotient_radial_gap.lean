-- Prove2me | Theorems.Thm_DerivativeChainContinuation_positive_quotient_radial_gap
-- name    : DerivativeChainContinuation.positive_quotient_radial_gap
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-26T23:40:51.273014+00:00
-- url     : https://prove2.me/theorems/b521648f-929c-407a-8acc-3981f74b77e7
-- title:
--   Arbitrary positive quotients give strict radial separation
-- statement:
--   A positive quotient Q∈ℝ[X] means Q≠0, Q splits over ℝ, and every element of its root multiset is strictly positive. Multiplicities are retained; nonzero constants satisfy this condition. For natural s,k and a real polynomial F, write W_(s,k,F)=sF+kXF′. Assume Q has positive degree, k≥2, s∈ℕ, Q(b)=0 and every real root of Q is at most b. Let t>0 be a maximal positive real root of W_(s,k,Q). Suppose R,x,y≥0, R^k=b, x^k=t, and either y=0 or Q(y^k)=0. If y<R, then R+y<2x.
-- source:
--   Private analytic checkpoint d69f598e254dee1915468fa93b3e33b8e1b5b7d6: research-results/unified-20261025/greedy/RAY_THEOREM.md, SHA-256 0d8a115e7059d0fae02ca0217cd20d64fc1baaf2a83795a4b171fa556be44a57. Local formal commit 7200800a2f88105b736aa292a1ec518302074d94 (not asserted pushed), submission_sync/new_formal/greedy/positive/PositiveRadialGap.lean, lines 57-96, SHA-256 9f6bd3c938573272d7f57312bcc230a26a34e3794af8c316febd05fbfc9f25cc.

import Mathlib
import Definitions.Def_DerivativeChainContinuation_PositiveSpokeClosure
import Definitions.Def_DerivativeChainContinuation_PositiveWeightedMidpoint
import Definitions.Def_DerivativeChainPrivate_foundations
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open Polynomial DerivativeChainPrivate
namespace DerivativeChainContinuation
end DerivativeChainContinuation
open DerivativeChainContinuation
open scoped BigOperators

theorem DerivativeChainContinuation.positive_quotient_radial_gap (s k : ℕ) (Q : Polynomial ℝ)
    (hQ : PositiveQuotient Q) (hQdegree : 0<Q.natDegree) (hk : 2 ≤ k)
    (b t : ℝ) (hB : Q.eval b=0) (hBmax : ∀ v : ℝ,Q.eval v=0 → v ≤ b)
    (ht : 0<t) (hroot : (positiveWeighted s k Q).eval t=0)
    (hmax : ∀ v : ℝ,0<v → (positiveWeighted s k Q).eval v=0 → v ≤ t)
    (R x y : ℝ) (hR : 0 ≤ R) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hRpow : R^k=b) (hxpow : x^k=t)
    (hparent : y=0 ∨ Q.eval (y^k)=0) (hyR : y<R) : R+y<2*x := by sorry
