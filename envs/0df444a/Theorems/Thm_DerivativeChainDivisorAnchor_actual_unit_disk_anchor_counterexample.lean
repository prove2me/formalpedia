-- Prove2me | Theorems.Thm_DerivativeChainDivisorAnchor_actual_unit_disk_anchor_counterexample
-- name    : DerivativeChainDivisorAnchor.actual_unit_disk_anchor_counterexample
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-26T21:18:20.474093+00:00
-- url     : https://prove2.me/theorems/9bf42f4d-f9ef-4fe7-9789-f31792cbf52a
-- title:
--   No finite universal divisor-anchor transport factor
-- statement:
--   For every real $K$, with no positivity assumption, there exists a natural $k\ge3$ with the following properties. For a natural $k\ge3$, set $m=4k^4$, $a=1/k^2$, $c=[1+(k-1)a^m]/k$, and $b=c^{1/m}$, where the last exponent is real exponentiation, exactly $\operatorname{Real.rpow}(c,(m:\mathbb R)^{-1})$. Set $B_k(X)=(X^m-a^m)(X^m-1)^{k-1}$ and $Q_k(X)=X^{m-1}(X^m-1)^{k-2}(X^m-b^m)$. These are the source and child denoted `obstructionSource` and `obstructionChild`; their definitions before the $k\ge3$ simplification use $n=m-2$ with natural subtraction and the base polynomial $X^{n+2}-1$, scaling its roots by $a$ or $b$. For any complex polynomial $T$, write $R_T$ for its multiset of complex roots, retaining every multiplicity, $d_T=T.\mathrm{natDegree}$, and $S(T,U)=\sum_{x\in R_T}\sum_{y\in R_U}|x-y|$, where both sums count root occurrences and ordered pairs, including the zero diagonal. A root slot is one occurrence in the multiset, not merely a distinct root value. Define $A(T,U)=[S(T,T)-S(T,U)]/d_T$. Define $W(T,U)$ as the real infimum of the set of costs $\sum_{i\in R_T}\sum_{j\in R_U}q_{ij}|i-j|$ over all real arrays on the two root-slot sets satisfying $q_{ij}\ge0$, $\sum_jq_{ij}=1/d_T$ for every source slot $i$, and $\sum_iq_{ij}=1/d_U$ for every target slot $j$. These are finite fractional couplings with only those nonnegativity and marginal constraints. Each occurrence has mass reciprocal to its polynomial's degree; there is no choice of distinct-root uniform law in this definition. The assertion is that $B_k$ is monic, $d_{B_k}=mk$, every root occurrence $i\in R_{B_k}$ satisfies $|i|\le1$, $\sum_{i\in R_{B_k}}i=0$, $(mk)^{-1}B_k'=Q_k$ as an identity of complex polynomials, $A(B_k,Q_k)>0$, and $K A(B_k,Q_k)<(d_{B_k}-1)W(B_k,Q_k)$. The zero sum is the unnormalized multiset sum, so it retains multiplicities. In this family $m,k,mk$, and $mk-1$ are positive; the source separately proves $0<a<1$, $0<b<1$, $b^m=[1+(k-1)a^m]/k$, $d_{Q_k}=mk-1$, $R_{B_k}=aR+(k-1)R$, and $R_{Q_k}=(m-1)\{0\}+(k-2)R+bR$, where $R$ is the root multiset of $X^m-1$ and multiplying a multiset by $a$ or $b$ means scaling each complex value, whereas a natural coefficient means repeating the multiset. These are the bridges to the actual derivative and root-slot law. For positive source and target degrees the constant product array $q_{ij}=1/(d_{B_k}d_{Q_k})$ is admissible and all costs are nonnegative, so this family uses a nonempty cost set bounded below.
-- source:
--   New formal source /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/new_formal/gini/DivisorAnchorNoGo.lean, lines 128-139, SHA-256 92c050c87bcf8bfe92676d362fb4304d232323d6882ed3da175723476b2518ba. This new Lean code is not present in commit 21d2a2ac5cd4b4e6263cbc715dd5f925427fc976. Mathematical source: private analytic checkpoint d69f598e254dee1915468fa93b3e33b8e1b5b7d6, /Users/amal/.codex/worktrees/q1-q2-unified-20261025/derivative-chain-prize/research-results/unified-20261025/proofs/TRANSPORT_NO_GO.md, Sections 1-5, SHA-256 65bd4415daa590832808ea570d591ae862689459fcd4ec90f9b1b278fa8104e2.

import Mathlib
import Definitions.Def_DerivativeChainGini_DivisorAnchorFunctional
import Definitions.Def_DerivativeChainGini_DivisorAnchorNoGo
import Definitions.Def_DerivativeChainGini_DivisorParameters
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

theorem DerivativeChainDivisorAnchor.actual_unit_disk_anchor_counterexample (K : ℝ) : ∃ k : ℕ, 3 ≤ k ∧
    (obstructionSource k).Monic ∧ (obstructionSource k).natDegree = orbitCount k*k ∧
    (∀ i : (obstructionSource k).roots, ‖(i:ℂ)‖ ≤ 1) ∧
    (obstructionSource k).roots.sum = 0 ∧
    C ((orbitCount k*k:ℂ)⁻¹)*(obstructionSource k).derivative = obstructionChild k ∧
    0 < rootAnchor (obstructionSource k) (obstructionChild k) ∧
    K*rootAnchor (obstructionSource k) (obstructionChild k) <
      (((obstructionSource k).natDegree:ℝ)-1)*uniformRootW1 (obstructionSource k) (obstructionChild k) := by sorry
