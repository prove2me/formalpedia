-- Prove2me | Theorems.Thm_DerivativeChainDivisorAnchor_actual_divisor_energy_bound
-- name    : DerivativeChainDivisorAnchor.actual_divisor_energy_bound
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-26T21:22:42.433648+00:00
-- url     : https://prove2.me/theorems/2160a7ff-67b8-45b4-8f9d-1deceee66285
-- title:
--   Absolute energy bound after shared-root cancellation
-- statement:
--   Let natural n, $k\ge3$, $0<a\le1$, $0<b\le1$, and $q=n+2$. For $P=P_{n,k,a}$, $Q=Q_{n,k,b}$, define $\mathcal E(P,Q)=S(P,Q)-S(P,P)/2-S(Q,Q)/2$. Then $$|\mathcal E(P,Q)|<8q^2.$$ No nonnegativity hypothesis on this signed energy is imposed.
-- source:
--   New formal source /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/new_formal/gini/PairDropSignedEnergy.lean, lines 134-157, SHA-256 57fd2bc6033ac8b7ccbf84566a3261affa8428115ba9997491d9ec0206473e16. This new Lean code is not present in commit 21d2a2ac5cd4b4e6263cbc715dd5f925427fc976. Mathematical source: private analytic checkpoint d69f598e254dee1915468fa93b3e33b8e1b5b7d6, /Users/amal/.codex/worktrees/q1-q2-unified-20261025/derivative-chain-prize/research-results/unified-20261025/proofs/TRANSPORT_NO_GO.md, Section 6, SHA-256 65bd4415daa590832808ea570d591ae862689459fcd4ec90f9b1b278fa8104e2.

import Mathlib
import Definitions.Def_DerivativeChainGini_DivisorActualFamily
import Definitions.Def_DerivativeChainGini_PairDropSignedEnergy
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

theorem DerivativeChainDivisorAnchor.actual_divisor_energy_bound (n k : ℕ) (hk : 3 ≤ k) (a b : ℝ)
    (ha : 0 < a) (ha1 : a ≤ 1) (hb : 0 < b) (hb1 : b ≤ 1) :
    |divisorEnergy (anchorSource n k a) (anchorChild n k b)| < 8*(n+2:ℝ)^2 := by sorry
