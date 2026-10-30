-- Prove2me | Theorems.Thm_DerivativeChainDivisorAnchor_explicit_pair_drop_k5
-- name    : DerivativeChainDivisorAnchor.explicit_pair_drop_k5
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-26T21:35:32.851606+00:00
-- url     : https://prove2.me/theorems/e4b6531a-5204-4e09-b20a-ad7d00eb6964
-- title:
--   A concrete powered pair-drop ratio above twenty-five sixths
-- statement:
--   This declaration has no parameters or hypotheses. For any complex polynomial $T$, write $R_T$ for its multiset of complex roots, retaining every multiplicity, $d_T=T.\mathrm{natDegree}$, and $S(T,U)=\sum_{x\in R_T}\sum_{y\in R_U}|x-y|$, where both sums count root occurrences and ordered pairs, including the zero diagonal. A root slot is one occurrence in the multiset, not merely a distinct root value. Define $A(T,U)=[S(T,T)-S(T,U)]/d_T$. Define $W(T,U)$ as the real infimum of the set of costs $\sum_{i\in R_T}\sum_{j\in R_U}q_{ij}|i-j|$ over all real arrays on the two root-slot sets satisfying $q_{ij}\ge0$, $\sum_jq_{ij}=1/d_T$ for every source slot $i$, and $\sum_iq_{ij}=1/d_U$ for every target slot $j$. These are finite fractional couplings with only those nonnegativity and marginal constraints. Each occurrence has mass reciprocal to its polynomial's degree; there is no choice of distinct-root uniform law in this definition. Fix $k=5$, $m=4\cdot5^4=2500$, $a=1/25$, $c=[1+4a^{2500}]/5$, $b=\operatorname{Real.rpow}(c,1/2500)$, $B=(X^{2500}-a^{2500})(X^{2500}-1)^4$, $Q=X^{2499}(X^{2500}-1)^3(X^{2500}-b^{2500})$, $r=12m=30000$, $P=B^r$, and $H=B^{r-1}Q$. These are `obstructionSource 5`, `obstructionChild 5`, `pairSource 5`, and `pairChild 5` as applicable. Let $N=d_P$, $D=[S(P,P)-S(H,H)]/2$, and $\rho=N(N-1)W(P,H)/D$, exactly `pairRatio 5`; the sums inside $D$ are unnormalized sums over ordered root occurrences. The declaration asserts jointly $N=375000000$, $25/6<\rho$, and $4<\rho$. It has no quantified parameter, and the two ratio inequalities are strict. The separately proved family bridges give $D>0$, $d_H=N-1$, $N^{-1}P'=H$, $R_P=30000R_B$, and $R_H=29999R_B+R_Q$; hence the ratio's denominator is positive for this specialization and $W$ uses finite uniform-root-occurrence couplings of these two concrete polynomials. Those bridge facts are not additional conjuncts in this fixed declaration. The positive source and child degrees also give a nonempty admissible cost set by the product coupling.
-- source:
--   New formal source /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/new_formal/gini/PairDropNoGo.lean, lines 163-167, SHA-256 3c0f5d48398e77c3f79f3ad99c46b208e604edb819ff48e371399c9f408e08b4. This new Lean code is not present in commit 21d2a2ac5cd4b4e6263cbc715dd5f925427fc976. Mathematical source: private analytic checkpoint d69f598e254dee1915468fa93b3e33b8e1b5b7d6, /Users/amal/.codex/worktrees/q1-q2-unified-20261025/derivative-chain-prize/research-results/unified-20261025/proofs/TRANSPORT_NO_GO.md, Section 6, SHA-256 65bd4415daa590832808ea570d591ae862689459fcd4ec90f9b1b278fa8104e2.

import Mathlib
import Definitions.Def_DerivativeChainGini_PairDropNoGo
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

theorem DerivativeChainDivisorAnchor.explicit_pair_drop_k5 :
    (pairSource 5).natDegree=375000000 ∧ (25/6:ℝ) < pairRatio 5 ∧ 4 < pairRatio 5 := by sorry
