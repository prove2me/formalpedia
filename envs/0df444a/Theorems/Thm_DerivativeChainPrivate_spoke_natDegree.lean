-- Prove2me | Theorems.Thm_DerivativeChainPrivate_spoke_natDegree
-- name    : DerivativeChainPrivate.spoke_natDegree
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-27T00:55:20.490254+00:00
-- url     : https://prove2.me/theorems/3ae05368-e514-4e9e-854b-85a178e01f66
-- title:
--   Degree of a nonzero spoke polynomial
-- statement:
--   For a nonzero real polynomial q and natural k>0,r, the complex spoke polynomial X^r q(X^k) has degree r+k·deg(q).
-- source:
--   Previously frozen formal source /private/tmp/prove2me-greedy-extensions-verified-20261026/RayTrinomial/SpokeRows.lean, lines 36-48, SHA-256 c08f5ce51bc6fe4a096ac924fc1de45ccf9631e93365f5e3169f976353e10784. Supporting statement retained exactly from the verified archive.

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

theorem DerivativeChainPrivate.spoke_natDegree (k r : ℕ) (q : Polynomial ℝ) (hq : q ≠ 0) (hk : 0 < k) :
    (spokePoly k r q).natDegree = r + k * q.natDegree := by sorry
