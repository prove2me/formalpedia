-- Prove2me | Theorems.Thm_DerivativeChainDivisorAnchor_orbitDistance_lower
-- name    : DerivativeChainDivisorAnchor.orbitDistance_lower
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-26T20:48:07.68786+00:00
-- url     : https://prove2.me/theorems/23f603fa-f33e-439e-a39f-6d93e2d0ef88
-- title:
--   Jensen lower bound for a zero-mean unit orbit
-- statement:
--   Let I be finite and nonempty, with $z:I\to\mathbb C$, $|z_i|=1$, and $\sum_i z_i=0$. For $R\ge0$ and arbitrary real S, let $H_z(R,S)=|I|^{-2}\sum_{i,j}|Rz_i-Sz_j|$. Then $$R\le H_z(R,S).$$
-- source:
--   New formal source /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/new_formal/gini/DivisorOrbitEstimates.lean, lines 47-59, SHA-256 976cdc2fd25c69d14b3ba5100e57d6535238194d321cb700cbdb6674ecfc9759. This new Lean code is not present in commit 21d2a2ac5cd4b4e6263cbc715dd5f925427fc976. Mathematical source: private analytic checkpoint d69f598e254dee1915468fa93b3e33b8e1b5b7d6, /Users/amal/.codex/worktrees/q1-q2-unified-20261025/derivative-chain-prize/research-results/unified-20261025/proofs/TRANSPORT_NO_GO.md, Sections 1-5, SHA-256 65bd4415daa590832808ea570d591ae862689459fcd4ec90f9b1b278fa8104e2.

import Mathlib
import Definitions.Def_DerivativeChainGini_DivisorOrbitEstimates
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
open DerivativeChainContinuation
open DerivativeChainDivisorAnchor

variable {ι : Type} [Fintype ι] [Nonempty ι]

theorem DerivativeChainDivisorAnchor.orbitDistance_lower (z : ι → ℂ) (hz : ∀ i, ‖z i‖=1)
    (hm : ∑ i, z i=0) (R S : ℝ) (hR : 0 ≤ R) : R ≤ orbitDistance z R S := by sorry
