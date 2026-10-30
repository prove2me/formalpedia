-- Prove2me | Theorems.Thm_DerivativeChainPrivate_real_splits_weighted_derivative
-- name    : DerivativeChainPrivate.real_splits_weighted_derivative
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-27T00:51:07.707419+00:00
-- url     : https://prove2.me/theorems/be34c7cb-6de9-41ec-9c7c-703d7c5bbd00
-- title:
--   Real-rootedness of a weighted Euler derivative
-- statement:
--   If a real polynomial q splits over ℝ, then (r+1)q+(k+1)Xq′ also splits over ℝ for all natural r,k.
-- source:
--   Previously frozen formal source /private/tmp/prove2me-greedy-extensions-verified-20261026/RayTrinomial/RayAlgebra.lean, lines 27-40, SHA-256 0f9163c6a3bb4b8ff3285d7a79e5775e363eecd1127633b9e70595c9f4943495. Supporting statement retained exactly from the verified archive.

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

theorem DerivativeChainPrivate.real_splits_weighted_derivative (q : Polynomial ℝ) (hq : q.Splits)
    (r k : ℕ) :
    (C (r + 1 : ℝ) * q + C (k + 1 : ℝ) * X * q.derivative).Splits := by sorry
