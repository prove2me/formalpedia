-- Prove2me | Theorems.Thm_DerivativeChainDivisorAnchor_root_transport_zero_lower
-- name    : DerivativeChainDivisorAnchor.root_transport_zero_lower
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-26T20:41:04.738045+00:00
-- url     : https://prove2.me/theorems/35eaf214-658b-409c-8543-9ad3841a4198
-- title:
--   Zero child slots force a uniform-root transport cost
-- statement:
--   Let $P,Q\in\mathbb C[X]$ have positive natural degrees $d_P,d_Q$. Assume $a\ge0$ and $|x|\ge a$ for every occurrence $x\in R_P$. If $m_Q(0)$ counts zero occurrences in $R_Q$, then $$a\,m_Q(0)/d_Q\le W(P,Q).$$ The infimum ranges over every nonnegative array with the uniform root-slot marginals. Its cost set is nonempty by the product coupling.
-- source:
--   New formal source /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/new_formal/gini/DivisorRootTransport.lean, lines 41-60, SHA-256 a89578b569d7880522341af1db3f795dacf9eb5b54dd27008909bb5cbbe53319. This new Lean code is not present in commit 21d2a2ac5cd4b4e6263cbc715dd5f925427fc976. Mathematical source: private analytic checkpoint d69f598e254dee1915468fa93b3e33b8e1b5b7d6, /Users/amal/.codex/worktrees/q1-q2-unified-20261025/derivative-chain-prize/research-results/unified-20261025/proofs/TRANSPORT_NO_GO.md, Sections 1-5, SHA-256 65bd4415daa590832808ea570d591ae862689459fcd4ec90f9b1b278fa8104e2.

import Mathlib
import Definitions.Def_DerivativeChainGini_DivisorAnchorFunctional
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

theorem DerivativeChainDivisorAnchor.root_transport_zero_lower (P Q : ℂ[X]) (hP : 0 < P.natDegree) (hQ : 0 < Q.natDegree)
    (a : ℝ) (ha : 0 ≤ a) (hmin : ∀ i : P.roots, a ≤ ‖(i:ℂ)‖) :
    a*(rootSum Q (fun y => if y=0 then 1 else 0)/(Q.natDegree:ℝ)) ≤ uniformRootW1 P Q := by sorry
