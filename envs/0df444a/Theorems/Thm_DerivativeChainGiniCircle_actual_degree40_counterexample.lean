-- Prove2me | Theorems.Thm_DerivativeChainGiniCircle_actual_degree40_counterexample
-- name    : DerivativeChainGiniCircle.actual_degree40_counterexample
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-26T23:10:19.647329+00:00
-- url     : https://prove2.me/theorems/bf6309d5-a5fc-41ef-96aa-05def5f800ea
-- title:
--   A degree-40 empirical-root counterexample to the circle Gini constant
-- statement:
--   This declaration has no parameters, hypotheses, existential choices, or additional typeclass assumptions. It concerns the fixed complex polynomial $P$, defined as $X^4\operatorname{base}(34)=X^4(X^{36}-1)$. For any complex polynomial $T$, let $R_T$ denote its multiset of complex roots with multiplicity, $d_T=T.\mathrm{natDegree}$, $E_T(f)=d_T^{-1}\sum_{x\in R_T}f(x)$ for every real-valued function $f$ on $\mathbb C$, $\mu_T=(\sum_{x\in R_T}x)/d_T$ in $\mathbb C$, $V(T)=d_T^{-1}\sum_{x\in R_T}|x-\mu_T|^2$, and $G(T)=E_T(x\mapsto E_T(y\mapsto|x-y|))=d_T^{-2}\sum_{x\in R_T}\sum_{y\in R_T}|x-y|$. All sums retain every root occurrence; the pair sum is over ordered pairs including the diagonal, and contains no factor $1/2$. Let $I$ be the finite root-slot type of the multiset of roots of $\operatorname{base}(34)=X^{36}-1$; it has 36 slots, each with complex value $z_i$, as specified by `rootSlot 34`. Let $J=\{\ast\}\sqcup I$, define the point at $\ast$ to be $0$ and the point at slot $i$ to be $z_i$, and define weights $w_\ast=1/10$ and $w_i=(1-1/10)/36=1/40$. These are precisely the specialized `point` and `childMass (1/10)` definitions. The declaration asserts all of the following jointly: $P=X^4(X^{36}-1)$; $P$ is monic; $d_P=40$; every root slot $i\in R_P$ satisfies $|i|\le1$; the unnormalized complex multiset sum $\sum_{i\in R_P}i=0$; for every function $f:\mathbb C\to\mathbb R$, with no continuity, measurability, boundedness, or integrability restriction, $\frac1{10}f(0)+\frac1{40}\sum_{i\in I}f(z_i)=E_P(f)$; $V(P)=9/10$; $G(P)=\frac{81}{100}\left(\frac1{18}\frac{\cos(\pi/72)}{\sin(\pi/72)}\right)+\frac9{50}$; $\frac{4\sqrt{V(P)}}{\pi}<G(P)$; and $\frac4\pi<\frac{G(P)}{\sqrt{V(P)}}$. The last two comparisons are strict; the root disk bound is non-strict. The square root is the nonnegative real square root, positive here because $V(P)=9/10$, and the denominator $\sin(\pi/72)$ is separately proved positive in the imported polygon source. The root-law bridge separately proved in the sources is $R_P=4\{0\}+R_{X^{36}-1}$ and $R_{X^{36}-1}=\sum_{j=0}^{35}\{\zeta^j\}$ for the defined primitive 36th root $\zeta=\exp(2\pi\mathrm i/36)$; the imported `polygonPoint` evaluates $\zeta^j$ on the integer representative $j\in\{0,\ldots,35\}$ of a residue class in $\mathbb Z/36\mathbb Z$. Thus the displayed law is uniform mass $1/40$ on each of the 40 root occurrences, represented by an aggregate mass $4/40$ at zero and one mass $1/40$ at each polygon root. The separate Gini bridge is $G(P)=\frac{81}{100}G(X^{36}-1)+\frac9{50}$ with $G(X^{36}-1)=\frac1{18}\cos(\pi/72)/\sin(\pi/72)$, deriving the asserted exact value from the finite pair sums. The final ratio normalizes this numerical Gini value by the square root of the empirical centered variance of the same polynomial; no rescaled polynomial is quantified. This declaration contains no coupling, transport cost, infimum, optimization, second polynomial, derivative, or normalized-derivative assertion.
-- source:
--   New formal source /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/new_formal/gini/GiniCircleCounterexample.lean, lines 121-131, SHA-256 9e9533a36951c231cc56cf2bd188fe0b95c41b04e1cf994d83ba4395c16e7d9b. This new Lean code is not present in commit 21d2a2ac5cd4b4e6263cbc715dd5f925427fc976. Mathematical source: private analytic checkpoint d69f598e254dee1915468fa93b3e33b8e1b5b7d6, /Users/amal/.codex/worktrees/q1-q2-unified-20261025/derivative-chain-prize/research-results/unified-20261025/audits/packets.md, Section 6, SHA-256 de7c92b1399b6ff5a045b7ab9eb15bf91ec45fde5384a6b1601888c1bef69c98.

import Mathlib
import Definitions.Def_DerivativeChainGini_GiniBinomialFamily
import Definitions.Def_DerivativeChainGini_GiniCandidateB
import Definitions.Def_DerivativeChainGini_GiniCircleCounterexample
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
open Polynomial DerivativeChainGiniFamily DerivativeChainDivisorAnchor DerivativeChainContinuation
open DerivativeChainGiniCircle

theorem DerivativeChainGiniCircle.actual_degree40_counterexample :
    source = (X^4*(X^36-1):ℂ[X]) ∧ source.Monic ∧ source.natDegree=40 ∧
    (∀ i : source.roots, ‖(i:ℂ)‖ ≤ 1) ∧ source.roots.sum=0 ∧
    (∀ f : ℂ → ℝ, (∑ i : Option (Slots 34), childMass (1/10) i*f (point (rootSlot 34) i)) = empiricalExpectation source f) ∧
    empiricalVariance source=9/10 ∧
    empiricalGini source=(81/100:ℝ)*((1/18:ℝ)*Real.cos (Real.pi/72)/Real.sin (Real.pi/72))+9/50 ∧
    4*Real.sqrt (empiricalVariance source)/Real.pi < empiricalGini source ∧
    4/Real.pi < empiricalGini source/Real.sqrt (empiricalVariance source) := by sorry
