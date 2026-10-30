-- Prove2me | Theorems.Thm_DerivativeChainDivisorAnchor_power_pair_drop
-- name    : DerivativeChainDivisorAnchor.power_pair_drop
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-26T21:24:48.178921+00:00
-- url     : https://prove2.me/theorems/7b1d04cd-cd47-4edf-b29e-49e86de3ebbe
-- title:
--   Exact root-pair drop identity under polynomial powers
-- statement:
--   Let $P,Q\in\mathbb C[X]$ be monic, with $d_P>0$, and let natural $r\ge1$. Put $U=P^r$, $V=P^{r-1}Q$, and $D(T,U)=[S(T,T)-S(U,U)]/2$. Then $$D(U,V)=r d_P A(P,Q)+\mathcal E(P,Q).$$ The statement has no derivative equation or specified degree for Q among its hypotheses.
-- source:
--   New formal source /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/new_formal/gini/PairDropPolynomialPower.lean, lines 44-59, SHA-256 019e5330fe3efd56675481c9b0abfb31b88cdff5feccdc7f4c4353b1f40e54b4. This new Lean code is not present in commit 21d2a2ac5cd4b4e6263cbc715dd5f925427fc976. Mathematical source: private analytic checkpoint d69f598e254dee1915468fa93b3e33b8e1b5b7d6, /Users/amal/.codex/worktrees/q1-q2-unified-20261025/derivative-chain-prize/research-results/unified-20261025/proofs/TRANSPORT_NO_GO.md, Section 6, SHA-256 65bd4415daa590832808ea570d591ae862689459fcd4ec90f9b1b278fa8104e2.

import Mathlib
import Definitions.Def_DerivativeChainGini_DivisorAnchorFunctional
import Definitions.Def_DerivativeChainGini_PairDropPolynomialPower
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

theorem DerivativeChainDivisorAnchor.power_pair_drop (P Q : ℂ[X]) (hP : P.Monic) (hQ : Q.Monic)
    (hn : 0 < P.natDegree) (r : ℕ) (hr : 1 ≤ r) :
    pairDrop (powerSource P r) (powerChild P Q r) =
      (r:ℝ)*(P.natDegree:ℝ)*rootAnchor P Q+divisorEnergy P Q := by sorry
