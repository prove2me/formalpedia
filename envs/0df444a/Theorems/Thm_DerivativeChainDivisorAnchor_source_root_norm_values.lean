-- Prove2me | Theorems.Thm_DerivativeChainDivisorAnchor_source_root_norm_values
-- name    : DerivativeChainDivisorAnchor.source_root_norm_values
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-26T20:43:30.544984+00:00
-- url     : https://prove2.me/theorems/7a3d6e0a-614a-4933-9380-65e6ca516968
-- title:
--   Root radii of the unequal two-orbit source
-- statement:
--   For natural $n,k$ and real $a>0$, put $F_n=X^{n+2}-1$ and $P=\operatorname{scaleRoots}(F_n,a)F_n^{k-1}$. Every occurrence $x\in R_P$ satisfies $$|x|=a\quad\text{or}\quad |x|=1.$$ There is no lower bound on k in this declaration; k-1 uses natural subtraction.
-- source:
--   New formal source /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/new_formal/gini/DivisorRootTransport.lean, lines 62-82, SHA-256 a89578b569d7880522341af1db3f795dacf9eb5b54dd27008909bb5cbbe53319. This new Lean code is not present in commit 21d2a2ac5cd4b4e6263cbc715dd5f925427fc976. Mathematical source: private analytic checkpoint d69f598e254dee1915468fa93b3e33b8e1b5b7d6, /Users/amal/.codex/worktrees/q1-q2-unified-20261025/derivative-chain-prize/research-results/unified-20261025/proofs/TRANSPORT_NO_GO.md, Sections 1-5, SHA-256 65bd4415daa590832808ea570d591ae862689459fcd4ec90f9b1b278fa8104e2.

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

attribute [local instance] Classical.propDecidable

theorem DerivativeChainDivisorAnchor.source_root_norm_values (n k : ℕ) (a : ℝ) (ha : 0 < a)
    (i : (anchorSource n k a).roots) : ‖(i:ℂ)‖=a ∨ ‖(i:ℂ)‖=1 := by sorry
