-- Prove2me | Theorems.Thm_DerivativeChainGini_actual_polynomial_counterexample
-- name    : DerivativeChainGini.actual_polynomial_counterexample
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-26T19:57:34.792169+00:00
-- url     : https://prove2.me/theorems/1817e334-da29-4288-8382-2518785e1be0
-- title:
--   Degree-16 obstruction to transport-Gini Candidate A
-- statement:
--   This declaration has no parameters or hypotheses. Let $(v_0,v_1,v_2,v_3,v_4)=(1,-1,\mathrm i,-\mathrm i,0)$ in $\mathbb C$, let parent multiplicities be $(4,4,4,4,0)$ and child multiplicities be $(3,3,3,3,3)$, and define $p_i$ as parent multiplicity divided by $16$ and $c_i$ as child multiplicity divided by $15$. For any real mass vector $u$ on these five indices, put $G(u)=\sum_{i=0}^4\sum_{j=0}^4u_i u_j|v_i-v_j|$. Put $W_5=\inf\{\sum_{i,j=0}^4q_{ij}|v_i-v_j|:q\in\mathbb R^{5\times5},\ q_{ij}\ge0,\ \sum_jq_{ij}=p_i\ (\text{every }i),\ \sum_iq_{ij}=c_j\ (\text{every }j)\}$; this is a real infimum over fractional finite couplings with no further constraints. Let $P=(X^4-1)^4$ and $Q=X^3(X^4-1)^3$, the defined `source` and `normalizedChild`. The declaration asserts, jointly: $P=(X^4-1)^4$; $P$ is monic; $d_P=16$; $\frac1{16}P'=X^3(X^4-1)^3$ as a complex polynomial identity; for each of the five indices $i$, $p_i=\#_{R_P}(v_i)/d_P$ and $c_i=\#_{R_Q}(v_i)/d_Q$, where $R_T$ is the root multiset and $\#_{R_T}$ counts multiplicity; $W_5=1/5$; $G(p)=(1+\sqrt2)/2$; $W_5-[(16/15)G(p)-G(c)]=(23-16\sqrt2)/75$; and $(16/15)G(p)-G(c)<W_5$. The mass laws use all root occurrences, not a uniform law on distinct root values: the source has four occurrences at each of $1,-1,\mathrm i,-\mathrm i$ and none at zero, while the child has three at every listed point and degree $15$, as identified by the separate root and degree bridge declarations. The five-point infimum has a feasible coupling with $q_{ii}=1/5$ for $i<4$, $q_{i4}=1/20$ for $i<4$, and all other entries zero; the source separately proves its cost and the lower bound for every feasible array. There are no free polynomial or degree quantifiers in this assertion.
-- source:
--   New formal source /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/new_formal/gini/GiniCounterexample.lean, lines 188-198, SHA-256 546b16561198697583702d7124535ecd4c397fb7d60be071297ec9b01bce2b7d. This new Lean code is not present in commit 21d2a2ac5cd4b4e6263cbc715dd5f925427fc976. Mathematical source: private analytic checkpoint d69f598e254dee1915468fa93b3e33b8e1b5b7d6, /Users/amal/.codex/worktrees/q1-q2-unified-20261025/derivative-chain-prize/research-results/unified-20261025/audits/packets.md, Section 4, SHA-256 de7c92b1399b6ff5a045b7ab9eb15bf91ec45fde5384a6b1601888c1bef69c98.

import Mathlib
import Definitions.Def_DerivativeChainGini_GiniCounterexample
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
open DerivativeChainGini



































open Polynomial

theorem DerivativeChainGini.actual_polynomial_counterexample :
    source = (X^4-1 : ℂ[X])^4 ∧ source.Monic ∧ source.natDegree = 16 ∧
    C (1/16 : ℂ) * source.derivative = X^3*(X^4-1)^3 ∧
    (∀ i : Fin 5, parentMass i = (source.roots.count (vertex i) : ℝ)/source.natDegree) ∧
    (∀ i : Fin 5, childMass i = (normalizedChild.roots.count (vertex i) : ℝ)/normalizedChild.natDegree) ∧
    optimalW1 = 1/5 ∧ gini parentMass = (1+Real.sqrt 2)/2 ∧
    optimalW1 - ((16/15 : ℝ)*gini parentMass-gini childMass) = (23-16*Real.sqrt 2)/75 ∧
    (16/15 : ℝ)*gini parentMass-gini childMass < optimalW1 := by sorry
