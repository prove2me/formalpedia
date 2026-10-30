-- Prove2me | Theorems.Thm_DerivativeChainDivisorAnchor_childRadius_drop
-- name    : DerivativeChainDivisorAnchor.childRadius_drop
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-26T21:13:41.827283+00:00
-- url     : https://prove2.me/theorems/070ee524-a579-4faf-8787-9fce15cbaf98
-- title:
--   A finite geometric-sum bound for the child-radius drop
-- statement:
--   For natural $k\ge3$, define $q=4k^4$, $a=1/k^2$, $c=[1+(k-1)a^q]/k$, and $b=\operatorname{Real.rpow}(c,1/q)$. Then $$q(1-b)\le k-1.$$ The estimate uses the exact relation b^q=c.
-- source:
--   New formal source /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/new_formal/gini/DivisorParameters.lean, lines 57-81, SHA-256 05f005ed42370b97ccf5a0f3c4842762723eb6fcae45b7da40c2513dfd710389. This new Lean code is not present in commit 21d2a2ac5cd4b4e6263cbc715dd5f925427fc976. Mathematical source: private analytic checkpoint d69f598e254dee1915468fa93b3e33b8e1b5b7d6, /Users/amal/.codex/worktrees/q1-q2-unified-20261025/derivative-chain-prize/research-results/unified-20261025/proofs/TRANSPORT_NO_GO.md, Sections 1-5, SHA-256 65bd4415daa590832808ea570d591ae862689459fcd4ec90f9b1b278fa8104e2.

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

theorem DerivativeChainDivisorAnchor.childRadius_drop (k : ℕ) (hk : 3 ≤ k) :
    (orbitCount k : ℝ)*(1-childRadius k) ≤ (k:ℝ)-1 := by sorry
