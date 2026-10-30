-- Prove2me | Theorems.Thm_DerivativeChainPrivate_spoke_derivative_parent_power
-- name    : DerivativeChainPrivate.spoke_derivative_parent_power
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-27T00:59:47.797483+00:00
-- url     : https://prove2.me/theorems/0c063ad9-0459-45c8-bb2a-f47a69e23f2b
-- title:
--   Real power and outward parent for a spoke critical point
-- statement:
--   Let k≥2, r<k and q be a nonzero real-rooted real polynomial. If the spoke polynomial X^r q(X^k) has degree at least two and w≠0 is one of its complex critical points, then w^k is real, equal to y, and q has a real root x with either 0<y≤x or x≤y<0.
-- source:
--   Previously frozen formal source /private/tmp/prove2me-greedy-extensions-verified-20261026/RayTrinomial/RayParent.lean, lines 7-58, SHA-256 081a4b76c683ce0717965704a7a9300b557969512b7eca54da2e100991418204. Supporting statement retained exactly from the verified archive.

import Mathlib
import Definitions.Def_DerivativeChainPrivate_SpokeRows
set_option autoImplicit false
namespace DerivativeChain
end DerivativeChain
namespace DerivativeChainClusterAnchor
end DerivativeChainClusterAnchor
namespace DerivativeChainContinuation
end DerivativeChainContinuation
namespace DerivativeChainExtremal
end DerivativeChainExtremal
namespace DerivativeChainPrefixLaws
end DerivativeChainPrefixLaws
namespace DerivativeChainPrivate
end DerivativeChainPrivate


set_option autoImplicit false
open DerivativeChainPrivate
open Polynomial

theorem DerivativeChainPrivate.spoke_derivative_parent_power (k r : ℕ) (q : Polynomial ℝ)
    (hk : 2 ≤ k) (hr : r < k) (hq : q.Splits) (hqne : q ≠ 0)
    (hdegree : 2 ≤ (spokePoly k r q).natDegree) (w : ℂ) (hw : w ≠ 0)
    (hz : (spokePoly k r q).derivative.eval w = 0) :
    ∃ y x : ℝ, w ^ k = (y : ℂ) ∧ q.eval x = 0 ∧
      ((0 < y ∧ y ≤ x) ∨ (y < 0 ∧ x ≤ y)) := by sorry
