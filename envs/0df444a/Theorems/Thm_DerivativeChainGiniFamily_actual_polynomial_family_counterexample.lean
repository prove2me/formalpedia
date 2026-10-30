-- Prove2me | Theorems.Thm_DerivativeChainGiniFamily_actual_polynomial_family_counterexample
-- name    : DerivativeChainGiniFamily.actual_polynomial_family_counterexample
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-26T20:00:02.118066+00:00
-- url     : https://prove2.me/theorems/7b50959c-3a83-4ec4-8e5e-c549e1321bc8
-- title:
--   No finite variance correction repairs the Gini transport increment
-- statement:
--   For every real constant $C$, with no sign restriction, there exists a natural number $n$ (the domain includes $0$ and has no additional lower-bound hypothesis) such that the following joint assertion holds. Put $m=n+2$, $P_n=(X^m-1)^{16}$, $Q_n=X^{n+1}(X^m-1)^{15}$, and $\varepsilon_n=(n+1)/[16(n+2)-1]$. Let $I_n$ be the finite root-slot type of the multiset of roots of $X^m-1$, retaining multiplicities; it has $m$ slots. On the disjoint union $J_n=\{\ast\}\sqcup I_n$, define $z_\ast=0$ and $z_i$ to be the complex root value of slot $i$, parent weights $p_\ast=0$, $p_i=1/m$, and child weights $c_\ast=\varepsilon_n$, $c_i=(1-\varepsilon_n)/m$. For a polynomial $T$, define $E_T(f)=(\sum_{x\in R_T}f(x))/d_T$, $V(T)=E_T(x\mapsto|x-(\sum_{y\in R_T}y)/d_T|^2)$, and $G(T)=E_T(x\mapsto E_T(y\mapsto|x-y|))$; all root sums retain multiplicity. Define $W_n$ as the real infimum of $\sum_{i,j\in J_n}q_{ij}|z_i-z_j|$ over all real nonnegative arrays with every row sum $p_i$ and every column sum $c_j$, without further constraints. The joint assertion is: $P_n=(X^{n+2}-1)^{16}$; $P_n$ is monic; $d_{P_n}=16(n+2)$; $[16(n+2)]^{-1}P_n'=X^{n+1}(X^{n+2}-1)^{15}$; for every function $f:\mathbb C\to\mathbb R$, $\sum_{i\in J_n}p_if(z_i)=E_{P_n}(f)$; independently for every such $f$, $\sum_{i\in J_n}c_if(z_i)=E_{Q_n}(f)$; $V(P_n)=1$; $W_n=\varepsilon_n$; and $G(P_n)-G(Q_n)+C\sqrt{V(P_n)}/d_{P_n}<W_n$. These universally quantified test functions need no measurability, continuity, boundedness, or integrability hypotheses because the expectations are finite sums. The root-law bridge declarations identify $R_{P_n}=16R_{X^m-1}$ and $R_{Q_n}=(n+1)\{0\}+15R_{X^m-1}$, with $d_{Q_n}=16m-1$. The optimization in this assertion is specifically the finite array problem on $J_n$, related to the polynomial root laws by the two displayed expectation identities. Its nonempty admissible set is exhibited separately by the array sending $\varepsilon_n/m$ from each root slot to $\ast$ and retaining $(1-\varepsilon_n)/m$ on that slot's diagonal; $0<\varepsilon_n<1/16$, each slot has norm $1$, and the source separately proves that every admissible array costs at least $\varepsilon_n$. The derivative is the actual formal derivative, scaled by the nonzero complex scalar $[16(n+2)]^{-1}$.
-- source:
--   New formal source /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/new_formal/gini/GiniCandidateB.lean, lines 188-206, SHA-256 92a353f1b6fb5dfa9cec8d6d22771e399a14cf2bd3ded30821e3fb3265bd35de. This new Lean code is not present in commit 21d2a2ac5cd4b4e6263cbc715dd5f925427fc976. Mathematical source: private analytic checkpoint d69f598e254dee1915468fa93b3e33b8e1b5b7d6, /Users/amal/.codex/worktrees/q1-q2-unified-20261025/derivative-chain-prize/research-results/unified-20261025/audits/packets.md, Section 5, SHA-256 de7c92b1399b6ff5a045b7ab9eb15bf91ec45fde5384a6b1601888c1bef69c98.

import Mathlib
import Definitions.Def_DerivativeChainGini_GiniBinomialFamily
import Definitions.Def_DerivativeChainGini_GiniCandidateB
import Definitions.Def_DerivativeChainGini_GiniFamilyTransport
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
open Polynomial DerivativeChainContinuation
open DerivativeChainGiniFamily

theorem DerivativeChainGiniFamily.actual_polynomial_family_counterexample (C : ℝ) : ∃ n : ℕ,
    source n = (X^(n+2)-1 : ℂ[X])^16 ∧ (source n).Monic ∧
    (source n).natDegree = 16*(n+2) ∧
    Polynomial.C ((16*(n+2) : ℂ)⁻¹)*(source n).derivative =
      X^(n+1)*(X^(n+2)-1)^15 ∧
    (∀ f : ℂ → ℝ, (∑ i : Option (Slots n), parentMass i*f (point (rootSlot n) i)) =
      empiricalExpectation (source n) f) ∧
    (∀ f : ℂ → ℝ, (∑ i : Option (Slots n), childMass (epsilon n) i*f (point (rootSlot n) i)) =
      empiricalExpectation (normalizedChild n) f) ∧
    empiricalVariance (source n) = 1 ∧
    optimalW1 (rootSlot n) (epsilon n) = epsilon n ∧
    empiricalGini (source n)-empiricalGini (normalizedChild n) +
      C*Real.sqrt (empiricalVariance (source n))/(source n).natDegree <
        optimalW1 (rootSlot n) (epsilon n) := by sorry
