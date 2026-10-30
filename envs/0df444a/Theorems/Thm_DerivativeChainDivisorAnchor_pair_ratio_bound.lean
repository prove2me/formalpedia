-- Prove2me | Theorems.Thm_DerivativeChainDivisorAnchor_pair_ratio_bound
-- name    : DerivativeChainDivisorAnchor.pair_ratio_bound
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-26T21:29:25.02184+00:00
-- url     : https://prove2.me/theorems/4bbec4e8-20ed-4ae5-8947-facf6e26cf6b
-- title:
--   Quantitative divergence of the explicit powered pair-drop ratio
-- statement:
--   For every natural $k$, under the sole hypothesis $k\ge3$, the following two conclusions hold simultaneously. For a natural $k\ge3$, set $m=4k^4$, $a=1/k^2$, $c=[1+(k-1)a^m]/k$, and $b=c^{1/m}$, where the last exponent is real exponentiation, exactly $\operatorname{Real.rpow}(c,(m:\mathbb R)^{-1})$. Set $B_k(X)=(X^m-a^m)(X^m-1)^{k-1}$ and $Q_k(X)=X^{m-1}(X^m-1)^{k-2}(X^m-b^m)$. These are the source and child denoted `obstructionSource` and `obstructionChild`; their definitions before the $k\ge3$ simplification use $n=m-2$ with natural subtraction and the base polynomial $X^{n+2}-1$, scaling its roots by $a$ or $b$. For any complex polynomial $T$, write $R_T$ for its multiset of complex roots, retaining every multiplicity, $d_T=T.\mathrm{natDegree}$, and $S(T,U)=\sum_{x\in R_T}\sum_{y\in R_U}|x-y|$, where both sums count root occurrences and ordered pairs, including the zero diagonal. A root slot is one occurrence in the multiset, not merely a distinct root value. Define $A(T,U)=[S(T,T)-S(T,U)]/d_T$. Define $W(T,U)$ as the real infimum of the set of costs $\sum_{i\in R_T}\sum_{j\in R_U}q_{ij}|i-j|$ over all real arrays on the two root-slot sets satisfying $q_{ij}\ge0$, $\sum_jq_{ij}=1/d_T$ for every source slot $i$, and $\sum_iq_{ij}=1/d_U$ for every target slot $j$. These are finite fractional couplings with only those nonnegativity and marginal constraints. Each occurrence has mass reciprocal to its polynomial's degree; there is no choice of distinct-root uniform law in this definition. Set $r=12m$, $P_k=B_k^r$ and $H_k=B_k^{r-1}Q_k$, exactly `pairSource` and `pairChild`. Set $N=d_{P_k}$, $D_k=[S(P_k,P_k)-S(H_k,H_k)]/2$, $C_k=(N-1)W(P_k,H_k)$, and $\rho_k=NC_k/D_k=N(N-1)W(P_k,H_k)/D_k$. Thus `pairDrop` is half the difference of unnormalized ordered root-pair distance sums, `poweredCost` is $C_k$, and `pairRatio` is $\rho_k$; none of these definitions inserts empirical-degree denominators into $S$. The conclusions are $D_k>0$ and $k^2/(k+1)<\rho_k$. The natural number $k$ is cast to a real number wherever it appears in these real inequalities; $k+1>0$, and $D_k>0$ is the first asserted conclusion, so both displayed denominators are nonzero on this domain. There is no free real constant, polynomial, coupling, or extra root-distribution hypothesis in this statement: its polynomials and laws are the explicitly defined family. The source separately proves $N=12m^2k=192k^9$, $d_{H_k}=N-1$, $R_{P_k}=rR_{B_k}$, $R_{H_k}=(r-1)R_{B_k}+R_{Q_k}$, and $N^{-1}P_k'=H_k$, so the finite coupling is between the multiplicity-weighted laws of an actual polynomial and its scaled derivative. Its admissible set is nonempty by the positive-degree product coupling. The algebraic bridge used in the proof is $D_k=N A(B_k,Q_k)+\mathcal E(B_k,Q_k)$ with $\mathcal E(T,U)=S(T,U)-S(T,T)/2-S(U,U)/2$; the accompanying proved bounds are $2/3\le A(B_k,Q_k)<3k+2$, $|\mathcal E(B_k,Q_k)|<8m^2$, and $(m-1)a\le C_k$. These bridge bounds are separate declarations, not extra hypotheses on $k$.
-- source:
--   New formal source /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/new_formal/gini/PairDropNoGo.lean, lines 80-127, SHA-256 3c0f5d48398e77c3f79f3ad99c46b208e604edb819ff48e371399c9f408e08b4. This new Lean code is not present in commit 21d2a2ac5cd4b4e6263cbc715dd5f925427fc976. Mathematical source: private analytic checkpoint d69f598e254dee1915468fa93b3e33b8e1b5b7d6, /Users/amal/.codex/worktrees/q1-q2-unified-20261025/derivative-chain-prize/research-results/unified-20261025/proofs/TRANSPORT_NO_GO.md, Section 6, SHA-256 65bd4415daa590832808ea570d591ae862689459fcd4ec90f9b1b278fa8104e2.

import Mathlib
import Definitions.Def_DerivativeChainGini_PairDropNoGo
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

theorem DerivativeChainDivisorAnchor.pair_ratio_bound (k : ℕ) (hk : 3 ≤ k) :
    0 < pairDrop (pairSource k) (pairChild k) ∧ (k:ℝ)^2/((k:ℝ)+1) < pairRatio k := by sorry
