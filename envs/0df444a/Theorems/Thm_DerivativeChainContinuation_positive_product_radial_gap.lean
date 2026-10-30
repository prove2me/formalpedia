-- Prove2me | Theorems.Thm_DerivativeChainContinuation_positive_product_radial_gap
-- name    : DerivativeChainContinuation.positive_product_radial_gap
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-26T23:36:48.998546+00:00
-- url     : https://prove2.me/theorems/d8a2001f-62d5-4be8-ad1a-268e5809e834
-- title:
--   Complete product roots give strict separation of lower parent radii
-- statement:
--   For natural s,k and a real polynomial F, write W_(s,k,F)=sF+kXF′. Let a∈ℝ^(n+1) be a monotone strictly positive tuple, F=∏_i(X-a_i), s∈ℕ and k≥2. Let t>0 be a root of W_(s,k,F) that is at least every positive real root of that polynomial. Suppose R,x,y≥0, R^k=a_n, x^k=t, and either y=0 or y^k=a_i for some i. If y<R, then R+y<2x.
-- source:
--   Private analytic checkpoint d69f598e254dee1915468fa93b3e33b8e1b5b7d6: research-results/unified-20261025/greedy/RAY_THEOREM.md, SHA-256 0d8a115e7059d0fae02ca0217cd20d64fc1baaf2a83795a4b171fa556be44a57. Local formal commit 7200800a2f88105b736aa292a1ec518302074d94 (not asserted pushed), submission_sync/new_formal/greedy/positive/PositiveRadialGap.lean, lines 7-55, SHA-256 9f6bd3c938573272d7f57312bcc230a26a34e3794af8c316febd05fbfc9f25cc.

import Mathlib
import Definitions.Def_DerivativeChainContinuation_PositiveWeightedMidpoint
import Definitions.Def_DerivativeChainContinuation_RealInterlacing
import Definitions.Def_DerivativeChainPrivate_foundations
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open Polynomial DerivativeChainPrivate
namespace DerivativeChainContinuation
end DerivativeChainContinuation
open DerivativeChainContinuation
open scoped BigOperators

theorem DerivativeChainContinuation.positive_product_radial_gap (n s k : ℕ) (a : Fin (n+1) → ℝ)
    (ha : Monotone a) (hpositive : ∀ i,0<a i) (hk : 2 ≤ k)
    (t : ℝ) (ht : 0<t) (hroot : (positiveWeighted s k (realRootProduct a)).eval t=0)
    (hmax : ∀ v : ℝ,0<v → (positiveWeighted s k (realRootProduct a)).eval v=0 → v ≤ t)
    (R x y : ℝ) (hR : 0 ≤ R) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hRpow : R^k=a (Fin.last n)) (hxpow : x^k=t)
    (hparent : y=0 ∨ ∃ i : Fin (n+1),y^k=a i) (hyR : y<R) : R+y<2*x := by sorry
