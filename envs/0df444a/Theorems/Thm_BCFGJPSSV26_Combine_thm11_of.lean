-- Prove2me | Theorems.Thm_BCFGJPSSV26_Combine_thm11_of
-- name    : BCFGJPSSV26.Combine.thm11_of
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T17:39:34.832503+00:00
-- url     : https://prove2.me/theorems/28b19de9-b288-4516-9547-06ff902e1804
-- title:
--   Theorem 1.1 (Part I) from Theorems 1.2 and 1.3 — the combination step
-- statement:
--   This is the combination step of Part I (arXiv:2610.18144), Section 1.1, step (ii): the statement of Theorem 1.1 (a randomized polynomial-time $1.95$-approximation for $k$-median) follows from the statements of Theorem 1.2 (pseudo-approximation) and Theorem 1.3 (stable instances).
--
--   **Setting.** An instance $I$ has $n$ clients, $m$ facilities, a number $k$ of centers and rational distances; it is *valid* if $k,m\ge 1$ and the distances form a pseudometric. For a nonempty set $S$ of facilities, $\mathrm{cost}(S)=\sum_j \min_{i\in S} d(j,i)$ over the clients $j$, and $\mathrm{opt}_\ell$ is the least cost of a nonempty set of at most $\ell$ facilities. $I$ is *$\beta$-stable* if $\mathrm{opt}_{k-1}\ge(1+\beta)\,\mathrm{opt}_k$ whenever $k\ge2$. $N$ is the bit length of the encoding of $I$. A deterministic algorithm is *polynomial-time* if a multitape Turing machine computes it within time and space polynomially bounded in $N$. A randomized algorithm *runs in time $O(T)$* if a deterministic multitape Turing machine computes it from the input $x$ and a coin string $r$ within $c\,(T(x)+|\langle x,r\rangle|+1)$ steps and cells for a constant $c$; probabilities are over uniformly random strings of exactly $T(x)$ coin flips.
--
--   **Hypotheses.**
--
--   1. (Theorem 1.2.) There is $C\in\mathbb R$ such that for every real $\varepsilon>0$ some deterministic polynomial-time algorithm outputs, on every valid instance, a nonempty list $S$ of distinct facilities with $|S|\le k+C\ln n/\varepsilon^2$ and $\mathrm{cost}(S)\le(1.9499+\varepsilon)\,\mathrm{opt}_k$.
--   2. (Theorem 1.3.) There are $a,b\in\mathbb N$, $C'\in\mathbb R$ and a randomized algorithm that, given $I$, a number $L$ in unary and a rational $\varepsilon$, runs in time $O(T)$ for $T=2^{eL}(N+2)^e$, $e=a(\lceil 1/\varepsilon\rceil+1)^b$, and on every valid instance with $k\le m$ outputs, for all $L$, $\varepsilon$ and all coins, a list of exactly $k$ distinct facilities; moreover, if $0<\varepsilon<1/200$ and $I$ is $\beta$-stable for some real $\beta>0$ with $1/\beta\le L$, then with probability at least $1-\varepsilon$ its cost is at most $(1.89+C'\varepsilon)\,\mathrm{opt}_k$.
--
--   **Conclusion.** There are $e\in\mathbb N$ and a randomized algorithm $A$ running in time $O((N+2)^e)$ such that, on every valid instance, $A$ outputs for all coins a nonempty list of at most $k$ distinct facilities, and
--
--   $$\Pr_r\big[\mathrm{cost}(A(I,r))\le 1.95\cdot\mathrm{opt}_k\big]\ \ge\ \tfrac23 .$$
--
--   **Role.** The main theorem (Theorem 1.1) is obtained by applying this implication to the proofs of Theorems 1.2 and 1.3, which enter only through their statements.
--
--   **Formalization Note** The three statements are word for word those of the main theorems. In hypothesis 2, $\lceil 1/\varepsilon\rceil$ is read as $0$ when $\varepsilon\le 0$, and $\ln 0=0$ in hypothesis 1.
-- source:
--   Buhai, Cohen-Addad, Fleischmann, Gupta, Jubés Monforte, Pittu, Stouras, Svensson, Vogl, A Better-than-2 Approximation for k-Median (Part I: arXiv:2610.18144, https://arxiv.org/abs/2610.18144; Part II: arXiv:2610.17172, https://arxiv.org/abs/2610.17172); Part I (arXiv:2610.18144), Section 1.1, step (ii) (Theorem 1.1 from Theorems 1.2 and 1.3). Lean source: `BCFGJPSSV26.Combine.thm11_of`, https://github.com/raresbuhai/formalization-of-my-research/blob/7abf511c7e99fd3fec3ff245a2b8d616ae17bc2c/BCFGJPSSV26/Combine.lean#L262-L312

module

public import Definitions.Def_BCFGJPSSV26_Combine_Analysis
public import Definitions.Def_BCFGJPSSV26_Combine_PolyTime
public import Definitions.Def_BCFGJPSSV26_Combine

set_option maxSynthPendingDepth 3

@[expose] public section

namespace BCFGJPSSV26.Combine

open Encoding

namespace Prm

variable (P : Prm)

end Prm

theorem thm11_of (h12 : Thm12) (h13 : Thm13) : Thm11 := by sorry

end BCFGJPSSV26.Combine
end
