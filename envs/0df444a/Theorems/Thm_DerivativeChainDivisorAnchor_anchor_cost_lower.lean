-- Prove2me | Theorems.Thm_DerivativeChainDivisorAnchor_anchor_cost_lower
-- name    : DerivativeChainDivisorAnchor.anchor_cost_lower
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-26T20:45:55.193914+00:00
-- url     : https://prove2.me/theorems/1c6b0899-e347-4914-ad46-14463c45498d
-- title:
--   Transport cost forced by the disappearing inner orbit
-- statement:
--   Let $n\in\mathbb N$, $k\ge3$, $0<a\le1$, and real $b\ne0$. For the defined unequal-orbit polynomials $P=P_{n,k,a}$ and $Q=Q_{n,k,b}$, $$(n+1)a\le(d_P-1)W(P,Q).$$ The separate power relation making Q the normalized derivative is not a hypothesis of this supporting estimate.
-- source:
--   New formal source /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/new_formal/gini/DivisorRootTransport.lean, lines 113-133, SHA-256 a89578b569d7880522341af1db3f795dacf9eb5b54dd27008909bb5cbbe53319. This new Lean code is not present in commit 21d2a2ac5cd4b4e6263cbc715dd5f925427fc976. Mathematical source: private analytic checkpoint d69f598e254dee1915468fa93b3e33b8e1b5b7d6, /Users/amal/.codex/worktrees/q1-q2-unified-20261025/derivative-chain-prize/research-results/unified-20261025/proofs/TRANSPORT_NO_GO.md, Sections 1-5, SHA-256 65bd4415daa590832808ea570d591ae862689459fcd4ec90f9b1b278fa8104e2.

import Mathlib
import Definitions.Def_DerivativeChainGini_DivisorActualFamily
import Definitions.Def_DerivativeChainGini_DivisorRootTransport
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

attribute [local instance] Classical.propDecidable

theorem DerivativeChainDivisorAnchor.anchor_cost_lower (n k : ℕ) (hk : 3 ≤ k) (a b : ℝ)
    (ha : 0 < a) (ha1 : a ≤ 1) (hb : b ≠ 0) :
    (n+1 : ℝ)*a ≤ (((anchorSource n k a).natDegree:ℝ)-1)*
      uniformRootW1 (anchorSource n k a) (anchorChild n k b) := by sorry
