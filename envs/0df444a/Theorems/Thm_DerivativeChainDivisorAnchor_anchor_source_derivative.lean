-- Prove2me | Theorems.Thm_DerivativeChainDivisorAnchor_anchor_source_derivative
-- name    : DerivativeChainDivisorAnchor.anchor_source_derivative
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-26T20:54:33.51819+00:00
-- url     : https://prove2.me/theorems/f7fe6b7f-ac27-4fff-95f3-1a940eb9bc95
-- title:
--   Exact derivative factorization of unequal binomial orbits
-- statement:
--   Let natural n, $k\ge2$, and real a,b satisfy $$b^{n+2}=[1+(k-1)a^{n+2}]/k.$$ Then the defined source and child obey the complex polynomial identity $$P_{n,k,a}^{\prime}=(n+2)k\,Q_{n,k,b}.$$ No positivity hypothesis on the radii is imposed.
-- source:
--   New formal source /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/new_formal/gini/DivisorActualFamily.lean, lines 67-88, SHA-256 9557ef1636f6669f928453ab9b9ca60695735ae8cfbe01b0db9bb987c90869c6. This new Lean code is not present in commit 21d2a2ac5cd4b4e6263cbc715dd5f925427fc976. Mathematical source: private analytic checkpoint d69f598e254dee1915468fa93b3e33b8e1b5b7d6, /Users/amal/.codex/worktrees/q1-q2-unified-20261025/derivative-chain-prize/research-results/unified-20261025/proofs/TRANSPORT_NO_GO.md, Sections 1-5, SHA-256 65bd4415daa590832808ea570d591ae862689459fcd4ec90f9b1b278fa8104e2.

import Mathlib
import Definitions.Def_DerivativeChainGini_DivisorActualFamily
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
open Polynomial DerivativeChainGiniFamily
open DerivativeChainDivisorAnchor

theorem DerivativeChainDivisorAnchor.anchor_source_derivative (n k : ℕ) (hk : 2 ≤ k) (a b : ℝ)
    (hbq : b^(n+2) = (1+(k-1 : ℝ)*a^(n+2))/(k:ℝ)) :
    (anchorSource n k a).derivative = C ((n+2)*k : ℂ) * anchorChild n k b := by sorry
