-- Prove2me | Theorems.Thm_DerivativeChainDivisorAnchor_obstruction_anchor_upper
-- name    : DerivativeChainDivisorAnchor.obstruction_anchor_upper
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-26T21:15:46.12015+00:00
-- url     : https://prove2.me/theorems/8d0975c4-74b2-4de8-ad4c-a17e18a7d084
-- title:
--   A linear anchor bound for the actual obstruction family
-- statement:
--   For natural $k\ge3$, let $q=4k^4$, $a=1/k^2$, and let b be the positive radius satisfying $b^q=[1+(k-1)a^q]/k$. Put $B_k=(X^q-a^q)(X^q-1)^{k-1}$ and $Q_k=X^{q-1}(X^q-1)^{k-2}(X^q-b^q)$. Then $$A(B_k,Q_k)<3k+2.$$ The family bridge proves $Q_k=(qk)^{-1}B_k^{\prime}$.
-- source:
--   New formal source /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/new_formal/gini/DivisorAnchorNoGo.lean, lines 47-58, SHA-256 92c050c87bcf8bfe92676d362fb4304d232323d6882ed3da175723476b2518ba. This new Lean code is not present in commit 21d2a2ac5cd4b4e6263cbc715dd5f925427fc976. Mathematical source: private analytic checkpoint d69f598e254dee1915468fa93b3e33b8e1b5b7d6, /Users/amal/.codex/worktrees/q1-q2-unified-20261025/derivative-chain-prize/research-results/unified-20261025/proofs/TRANSPORT_NO_GO.md, Sections 1-5, SHA-256 65bd4415daa590832808ea570d591ae862689459fcd4ec90f9b1b278fa8104e2.

import Mathlib
import Definitions.Def_DerivativeChainGini_DivisorAnchorNoGo
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

theorem DerivativeChainDivisorAnchor.obstruction_anchor_upper (k : ℕ) (hk : 3 ≤ k) : obstructionAnchor k < 3*(k:ℝ)+2 := by sorry
