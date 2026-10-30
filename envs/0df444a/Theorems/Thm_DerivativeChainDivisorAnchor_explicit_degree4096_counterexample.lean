-- Prove2me | Theorems.Thm_DerivativeChainDivisorAnchor_explicit_degree4096_counterexample
-- name    : DerivativeChainDivisorAnchor.explicit_degree4096_counterexample
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-26T21:20:30.42045+00:00
-- url     : https://prove2.me/theorems/77bee90a-9fb3-4fdc-8802-105f39b45ca0
-- title:
--   Explicit degree-4096 violation of the anchor factor four
-- statement:
--   This declaration has no parameters or hypotheses. For any complex polynomial $T$, write $R_T$ for its multiset of complex roots, retaining every multiplicity, $d_T=T.\mathrm{natDegree}$, and $S(T,U)=\sum_{x\in R_T}\sum_{y\in R_U}|x-y|$, where both sums count root occurrences and ordered pairs, including the zero diagonal. A root slot is one occurrence in the multiset, not merely a distinct root value. Define $A(T,U)=[S(T,T)-S(T,U)]/d_T$. Define $W(T,U)$ as the real infimum of the set of costs $\sum_{i\in R_T}\sum_{j\in R_U}q_{ij}|i-j|$ over all real arrays on the two root-slot sets satisfying $q_{ij}\ge0$, $\sum_jq_{ij}=1/d_T$ for every source slot $i$, and $\sum_iq_{ij}=1/d_U$ for every target slot $j$. These are finite fractional couplings with only those nonnegativity and marginal constraints. Each occurrence has mass reciprocal to its polynomial's degree; there is no choice of distinct-root uniform law in this definition. Put $m=1024$, $a=1/16$, $c=[1+3a^{1024}]/4$, and $b=\operatorname{Real.rpow}(c,1/1024)$. The defined polynomials at $k=4$ are $B=(X^{1024}-a^{1024})(X^{1024}-1)^3$ and $Q=X^{1023}(X^{1024}-1)^2(X^{1024}-b^{1024})$. Write $A_4=A(B,Q)$ and $C_4=(d_B-1)W(B,Q)$, exactly `obstructionAnchor 4` and `obstructionCost 4`. The declaration asserts, jointly, the displayed formula for $B$ with $a=1/16$; $d_B=4096$; $2/3\le A_4$; $A_4<14$; $1023/16\le C_4$; $1023/224<C_4/A_4$; and $4<C_4/A_4$. The assertion is for these fixed polynomials and quantities, with no existential or universal parameter binder. In particular, its denominator is positive by the asserted lower bound $A_4\ge2/3$. The actual derivative relation $4096^{-1}B'=Q$, the target degree $4095$, and the multiplicity formulas $R_B=aR+3R$ and $R_Q=1023\{0\}+2R+bR$ for $R=R_{X^{1024}-1}$ are separately proved bridges supplied by the family definitions and lemmas, rather than additional conjuncts of this fixed declaration. The finite root-coupling cost set here is nonempty by the separately proved product coupling for positive degrees.
-- source:
--   New formal source /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/new_formal/gini/DivisorAnchorNoGo.lean, lines 93-113, SHA-256 92c050c87bcf8bfe92676d362fb4304d232323d6882ed3da175723476b2518ba. This new Lean code is not present in commit 21d2a2ac5cd4b4e6263cbc715dd5f925427fc976. Mathematical source: private analytic checkpoint d69f598e254dee1915468fa93b3e33b8e1b5b7d6, /Users/amal/.codex/worktrees/q1-q2-unified-20261025/derivative-chain-prize/research-results/unified-20261025/proofs/TRANSPORT_NO_GO.md, Sections 1-5, SHA-256 65bd4415daa590832808ea570d591ae862689459fcd4ec90f9b1b278fa8104e2.

import Mathlib
import Definitions.Def_DerivativeChainGini_DivisorAnchorNoGo
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

set_option maxRecDepth 20000 in
theorem DerivativeChainDivisorAnchor.explicit_degree4096_counterexample :
    obstructionSource 4 = (X^1024-C ((1/16:ℂ)^1024))*(X^1024-1)^3 ∧
    (obstructionSource 4).natDegree = 4096 ∧
    (2/3:ℝ) ≤ obstructionAnchor 4 ∧ obstructionAnchor 4 < 14 ∧
    (1023/16:ℝ) ≤ obstructionCost 4 ∧
    (1023/224:ℝ) < obstructionCost 4/obstructionAnchor 4 ∧
    4 < obstructionCost 4/obstructionAnchor 4 := by sorry
