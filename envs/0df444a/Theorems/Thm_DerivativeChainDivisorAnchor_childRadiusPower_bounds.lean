-- Prove2me | Theorems.Thm_DerivativeChainDivisorAnchor_childRadiusPower_bounds
-- name    : DerivativeChainDivisorAnchor.childRadiusPower_bounds
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-26T21:04:26.804774+00:00
-- url     : https://prove2.me/theorems/38f755d2-77e5-42ca-9923-5f1bc57c47ff
-- title:
--   Bounds on the child-radius power
-- statement:
--   For natural $k\ge3$, set $q=4k^4$, $a=1/k^2$, and $c=[1+(k-1)a^q]/k$. Jointly, $$0<c,\qquad c<1,\qquad 1/k\le c.$$ These bounds justify the positive real qth-root construction.
-- source:
--   New formal source /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/new_formal/gini/DivisorParameters.lean, lines 31-44, SHA-256 05f005ed42370b97ccf5a0f3c4842762723eb6fcae45b7da40c2513dfd710389. This new Lean code is not present in commit 21d2a2ac5cd4b4e6263cbc715dd5f925427fc976. Mathematical source: private analytic checkpoint d69f598e254dee1915468fa93b3e33b8e1b5b7d6, /Users/amal/.codex/worktrees/q1-q2-unified-20261025/derivative-chain-prize/research-results/unified-20261025/proofs/TRANSPORT_NO_GO.md, Sections 1-5, SHA-256 65bd4415daa590832808ea570d591ae862689459fcd4ec90f9b1b278fa8104e2.

import Mathlib
import Definitions.Def_DerivativeChainGini_DivisorParameters
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
open DerivativeChainDivisorAnchor

theorem DerivativeChainDivisorAnchor.childRadiusPower_bounds (k : ℕ) (hk : 3 ≤ k) :
    0 < childRadiusPower k ∧ childRadiusPower k < 1 ∧ 1/(k:ℝ) ≤ childRadiusPower k := by sorry
