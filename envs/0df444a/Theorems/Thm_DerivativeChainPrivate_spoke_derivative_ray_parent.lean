-- Prove2me | Theorems.Thm_DerivativeChainPrivate_spoke_derivative_ray_parent
-- name    : DerivativeChainPrivate.spoke_derivative_ray_parent
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-27T01:01:53.656321+00:00
-- url     : https://prove2.me/theorems/079aadfc-fe59-4d7e-8190-2b8a00374b18
-- title:
--   A nonzero spoke critical point has an outward root on its ray
-- statement:
--   For k≥2, r<k and nonzero real-rooted q, if the spoke polynomial has degree at least two and w≠0 is a critical point, there is a real t≥1 such that tw is an actual root of that spoke polynomial.
-- source:
--   Previously frozen formal source /private/tmp/prove2me-greedy-extensions-verified-20261026/RayTrinomial/RayParent.lean, lines 60-84, SHA-256 081a4b76c683ce0717965704a7a9300b557969512b7eca54da2e100991418204. Supporting statement retained exactly from the verified archive.

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

theorem DerivativeChainPrivate.spoke_derivative_ray_parent (k r : ℕ) (q : Polynomial ℝ)
    (hk : 2 ≤ k) (hr : r < k) (hq : q.Splits) (hqne : q ≠ 0)
    (hdegree : 2 ≤ (spokePoly k r q).natDegree) (w : ℂ) (hw : w ≠ 0)
    (hz : (spokePoly k r q).derivative.eval w = 0) :
    ∃ t : ℝ, 1 ≤ t ∧ (spokePoly k r q).eval ((t : ℂ) * w) = 0 := by sorry
