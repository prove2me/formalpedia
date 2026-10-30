-- Prove2me | Theorems.Thm_DerivativeChainPrivate_spoke_geodesic
-- name    : DerivativeChainPrivate.spoke_geodesic
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-27T01:03:35.270983+00:00
-- url     : https://prove2.me/theorems/05b54f33-9363-4e3d-b6e5-f0962e0439d0
-- title:
--   Complete telescoping root chain for mixed-sign real spokes
-- statement:
--   For k≥2, r<k and nonzero real-rooted q, suppose X^r q(X^k) has degree n+1. There is a sequence z starting at zero, with z_i an actual root of its (n−i)-th derivative for every i<n+1, and |z_(i+1)−z_i|=|z_(i+1)|−|z_i| for every i<n. Roots of q may have either sign.
-- source:
--   Previously frozen formal source /private/tmp/prove2me-greedy-extensions-verified-20261026/RayTrinomial/RayChain.lean, lines 9-82, SHA-256 a6d60f43a655863ce55dffcfe62b804439a649e12a9dd8e98ca704e33afbd50b. Supporting statement retained exactly from the verified archive.

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
open scoped BigOperators
open DerivativeChainPrivate
open Polynomial

theorem DerivativeChainPrivate.spoke_geodesic (n k r : ℕ) (q : Polynomial ℝ) (hk : 2 ≤ k)
    (hr : r < k) (hq : q.Splits) (hqne : q ≠ 0)
    (hdegree : (spokePoly k r q).natDegree = n + 1) :
    ∃ z : ℕ → ℂ, z 0 = 0 ∧
      (∀ i < n + 1, (Polynomial.derivative^[n - i] (spokePoly k r q)).eval (z i) = 0) ∧
      (∀ i < n, ‖z (i + 1) - z i‖ = ‖z (i + 1)‖ - ‖z i‖) := by sorry
