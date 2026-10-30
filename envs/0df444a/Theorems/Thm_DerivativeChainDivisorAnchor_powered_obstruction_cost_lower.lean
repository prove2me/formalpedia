-- Prove2me | Theorems.Thm_DerivativeChainDivisorAnchor_powered_obstruction_cost_lower
-- name    : DerivativeChainDivisorAnchor.powered_obstruction_cost_lower
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-26T21:27:18.488489+00:00
-- url     : https://prove2.me/theorems/f77a425b-8324-42b0-afda-f23d11ed242b
-- title:
--   Transport lower bound for every positive power of the obstruction
-- statement:
--   Let natural $k\ge3$ and $r\ge1$, with $q=4k^4$, $a=1/k^2$, and the actual source and child $B_k,Q_k$. Put $U=B_k^r$, $V=B_k^{r-1}Q_k$. Then $$(q-1)a\le(d_U-1)W(U,V).$$ Every root-slot multiplicity introduced by the power is retained.
-- source:
--   New formal source /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/new_formal/gini/PairDropPolynomialPower.lean, lines 86-127, SHA-256 019e5330fe3efd56675481c9b0abfb31b88cdff5feccdc7f4c4353b1f40e54b4. This new Lean code is not present in commit 21d2a2ac5cd4b4e6263cbc715dd5f925427fc976. Mathematical source: private analytic checkpoint d69f598e254dee1915468fa93b3e33b8e1b5b7d6, /Users/amal/.codex/worktrees/q1-q2-unified-20261025/derivative-chain-prize/research-results/unified-20261025/proofs/TRANSPORT_NO_GO.md, Section 6, SHA-256 65bd4415daa590832808ea570d591ae862689459fcd4ec90f9b1b278fa8104e2.

import Mathlib
import Definitions.Def_DerivativeChainGini_DivisorAnchorNoGo
import Definitions.Def_DerivativeChainGini_DivisorParameters
import Definitions.Def_DerivativeChainGini_DivisorRootTransport
import Definitions.Def_DerivativeChainGini_PairDropPolynomialPower
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

theorem DerivativeChainDivisorAnchor.powered_obstruction_cost_lower (k r : ℕ) (hk : 3 ≤ k) (hr : 1 ≤ r) :
    ((orbitCount k:ℝ)-1)*innerRadius k ≤
      (((powerSource (obstructionSource k) r).natDegree:ℝ)-1)*
        uniformRootW1 (powerSource (obstructionSource k) r) (powerChild (obstructionSource k) (obstructionChild k) r) := by sorry
