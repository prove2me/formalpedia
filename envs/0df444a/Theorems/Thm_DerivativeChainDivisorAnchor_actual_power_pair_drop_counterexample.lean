-- Prove2me | Theorems.Thm_DerivativeChainDivisorAnchor_actual_power_pair_drop_counterexample
-- name    : DerivativeChainDivisorAnchor.actual_power_pair_drop_counterexample
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-26T21:32:26.652975+00:00
-- url     : https://prove2.me/theorems/a7080859-41d0-42a5-a3fe-4ae4a6eea80f
-- title:
--   No finite pair-distance-drop factor on explicit polynomial powers
-- statement:
--   For every real $K$, with no sign hypothesis, there exists a natural $k\ge3$ for which the following joint assertion holds. For a natural $k\ge3$, set $m=4k^4$, $a=1/k^2$, $c=[1+(k-1)a^m]/k$, and $b=c^{1/m}$, where the last exponent is real exponentiation, exactly $\operatorname{Real.rpow}(c,(m:\mathbb R)^{-1})$. Set $B_k(X)=(X^m-a^m)(X^m-1)^{k-1}$ and $Q_k(X)=X^{m-1}(X^m-1)^{k-2}(X^m-b^m)$. These are the source and child denoted `obstructionSource` and `obstructionChild`; their definitions before the $k\ge3$ simplification use $n=m-2$ with natural subtraction and the base polynomial $X^{n+2}-1$, scaling its roots by $a$ or $b$. For any complex polynomial $T$, write $R_T$ for its multiset of complex roots, retaining every multiplicity, $d_T=T.\mathrm{natDegree}$, and $S(T,U)=\sum_{x\in R_T}\sum_{y\in R_U}|x-y|$, where both sums count root occurrences and ordered pairs, including the zero diagonal. A root slot is one occurrence in the multiset, not merely a distinct root value. Define $A(T,U)=[S(T,T)-S(T,U)]/d_T$. Define $W(T,U)$ as the real infimum of the set of costs $\sum_{i\in R_T}\sum_{j\in R_U}q_{ij}|i-j|$ over all real arrays on the two root-slot sets satisfying $q_{ij}\ge0$, $\sum_jq_{ij}=1/d_T$ for every source slot $i$, and $\sum_iq_{ij}=1/d_U$ for every target slot $j$. These are finite fractional couplings with only those nonnegativity and marginal constraints. Each occurrence has mass reciprocal to its polynomial's degree; there is no choice of distinct-root uniform law in this definition. Set $r=12m$, $P_k=B_k^r$ and $H_k=B_k^{r-1}Q_k$, exactly `pairSource` and `pairChild`. Set $N=d_{P_k}$, $D_k=[S(P_k,P_k)-S(H_k,H_k)]/2$, $C_k=(N-1)W(P_k,H_k)$, and $\rho_k=NC_k/D_k=N(N-1)W(P_k,H_k)/D_k$. Thus `pairDrop` is half the difference of unnormalized ordered root-pair distance sums, `poweredCost` is $C_k$, and `pairRatio` is $\rho_k$; none of these definitions inserts empirical-degree denominators into $S$. It asserts $P_k=B_k^{12m}$, that $P_k$ is monic, $N=192k^9$, that every root occurrence of $P_k$ has norm at most $1$, that $\sum_{i\in R_{P_k}}i=0$, that $N^{-1}P_k'=H_k$ as an identity of complex polynomials, that $D_k>0$, and that $K D_k<N(N-1)W(P_k,H_k)$. The natural exponent $r-1$ is subtraction in $\mathbb N$; here $r\ge1$, so it is the ordinary predecessor and no truncated-subtraction edge case occurs. The root and derivative bridges separately proved in the sources are $R_{P_k}=rR_{B_k}$, $R_{H_k}=(r-1)R_{B_k}+R_{Q_k}$, $d_{H_k}=N-1$, and $(P_k)'=N H_k$. Thus the root law optimized by $W$ is uniform over all $N$ and $N-1$ multiset occurrences, respectively, including the repeated roots from the polynomial power. The target child is specifically $B_k^{r-1}Q_k$, defined before asserting its equality with the scaled actual derivative. The positive degrees give a nonempty admissible coupling set via the product array and nonnegative costs. The source also proves the bridge $D_k=N A(B_k,Q_k)+\mathcal E(B_k,Q_k)$, where $\mathcal E(T,U)=S(T,U)-S(T,T)/2-S(U,U)/2$; this identity relates the half-pair-sum difference to the earlier anchor without replacing $W$ by another optimization.
-- source:
--   New formal source /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/new_formal/gini/PairDropNoGo.lean, lines 151-161, SHA-256 3c0f5d48398e77c3f79f3ad99c46b208e604edb819ff48e371399c9f408e08b4. This new Lean code is not present in commit 21d2a2ac5cd4b4e6263cbc715dd5f925427fc976. Mathematical source: private analytic checkpoint d69f598e254dee1915468fa93b3e33b8e1b5b7d6, /Users/amal/.codex/worktrees/q1-q2-unified-20261025/derivative-chain-prize/research-results/unified-20261025/proofs/TRANSPORT_NO_GO.md, Section 6, SHA-256 65bd4415daa590832808ea570d591ae862689459fcd4ec90f9b1b278fa8104e2.

import Mathlib
import Definitions.Def_DerivativeChainGini_DivisorAnchorNoGo
import Definitions.Def_DerivativeChainGini_DivisorParameters
import Definitions.Def_DerivativeChainGini_DivisorRootTransport
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

theorem DerivativeChainDivisorAnchor.actual_power_pair_drop_counterexample (K : ℝ) : ∃ k : ℕ, 3 ≤ k ∧
    pairSource k=(obstructionSource k)^(12*orbitCount k) ∧ (pairSource k).Monic ∧
    (pairSource k).natDegree=192*k^9 ∧
    (∀ i : (pairSource k).roots, ‖(i:ℂ)‖ ≤ 1) ∧ (pairSource k).roots.sum=0 ∧
    C (((pairSource k).natDegree:ℂ)⁻¹)*(pairSource k).derivative=pairChild k ∧
    0 < pairDrop (pairSource k) (pairChild k) ∧
    K*pairDrop (pairSource k) (pairChild k) <
      (pairSource k).natDegree*(((pairSource k).natDegree:ℝ)-1)*uniformRootW1 (pairSource k) (pairChild k) := by sorry
