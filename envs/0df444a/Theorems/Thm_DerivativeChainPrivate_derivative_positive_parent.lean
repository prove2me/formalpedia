-- Prove2me | Theorems.Thm_DerivativeChainPrivate_derivative_positive_parent
-- name    : DerivativeChainPrivate.derivative_positive_parent
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-27T00:53:38.817009+00:00
-- url     : https://prove2.me/theorems/7ae21817-c9bc-4eca-b181-5fe8283573df
-- title:
--   A real derivative root has a root on its right
-- statement:
--   If q is a nonzero real-rooted real polynomial of positive degree and q′(y)=0 for real y, then q has a real root x≥y.
-- source:
--   Previously frozen formal source /private/tmp/prove2me-greedy-extensions-verified-20261026/RayTrinomial/RayAlgebra.lean, lines 103-129, SHA-256 0f9163c6a3bb4b8ff3285d7a79e5775e363eecd1127633b9e70595c9f4943495. Supporting statement retained exactly from the verified archive.

import Mathlib
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

theorem DerivativeChainPrivate.derivative_positive_parent (q : Polynomial ℝ) (hq : q ≠ 0) (hs : q.Splits)
    (hdeg : 0 < q.natDegree) (y : ℝ) (hz : q.derivative.eval y = 0) :
    ∃ x ∈ q.roots, y ≤ x := by sorry
