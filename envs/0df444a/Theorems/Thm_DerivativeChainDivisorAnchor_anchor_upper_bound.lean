-- Prove2me | Theorems.Thm_DerivativeChainDivisorAnchor_anchor_upper_bound
-- name    : DerivativeChainDivisorAnchor.anchor_upper_bound
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-26T21:11:05.429069+00:00
-- url     : https://prove2.me/theorems/98b24e24-27c2-4393-875d-a2d02b3c0dc2
-- title:
--   Elementary upper bound for the two-orbit anchor
-- statement:
--   For natural n, $k\ge3$, $0<a\le1$, and $0<b\le1$, put $q=n+2$, $P=P_{n,k,a}$, and $Q=Q_{n,k,b}$. Then $$A(P,Q)<q\left(\frac{a}{2k}+\frac{a^2}{2}+1-b\right)+1.$$ The derivative power relation is supplied separately in the final family.
-- source:
--   New formal source /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/new_formal/gini/DivisorAnchorBounds.lean, lines 35-69, SHA-256 00eab1559ae822d709d6486c1a6771b3371817193203a6bed95cb4ca1b983593. This new Lean code is not present in commit 21d2a2ac5cd4b4e6263cbc715dd5f925427fc976. Mathematical source: private analytic checkpoint d69f598e254dee1915468fa93b3e33b8e1b5b7d6, /Users/amal/.codex/worktrees/q1-q2-unified-20261025/derivative-chain-prize/research-results/unified-20261025/proofs/TRANSPORT_NO_GO.md, Sections 1-5, SHA-256 65bd4415daa590832808ea570d591ae862689459fcd4ec90f9b1b278fa8104e2.

import Mathlib
import Definitions.Def_DerivativeChainGini_DivisorActualFamily
import Definitions.Def_DerivativeChainGini_DivisorAnchorFunctional
set_option autoImplicit false
namespace DerivativeChain
end DerivativeChain
namespace DerivativeChainContinuation
end DerivativeChainContinuation
namespace DerivativeChainDivisorAnchor
end DerivativeChainDivisorAnchor
namespace DerivativeChainGini
end DerivativeChainGini
namespace DerivativeChainGiniCircle
end DerivativeChainGiniCircle
namespace DerivativeChainGiniFamily
end DerivativeChainGiniFamily
namespace DerivativeChainPrivate
end DerivativeChainPrivate

set_option autoImplicit false
open scoped BigOperators
open DerivativeChainGiniFamily
open DerivativeChainDivisorAnchor

theorem DerivativeChainDivisorAnchor.anchor_upper_bound (n k : ℕ) (hk : 3 ≤ k) (a b : ℝ)
    (ha : 0 < a) (ha1 : a ≤ 1) (hb : 0 < b) (hb1 : b ≤ 1) :
    rootAnchor (anchorSource n k a) (anchorChild n k b) <
      (n+2 : ℝ)*(a/(2*(k:ℝ))+a^2/2+(1-b))+1 := by sorry
