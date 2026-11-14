-- Prove2me | Theorems.Thm_BCFGJPSSV26_Stable_stable_main
-- name    : BCFGJPSSV26.Stable.stable_main
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T17:56:07.56372+00:00
-- url     : https://prove2.me/theorems/4a4599b0-48cf-429d-bf20-ff468495668e
-- title:
--   Theorem 1.1 (Part II) — $(1.89+O(\varepsilon))$-approximation for $\beta$-stable $k$-median instances
-- statement:
--   This is Theorem 1.1 of Part II (Theorem 1.3 of Part I): one randomized algorithm that, on $\beta$-stable $k$-median instances, outputs $k$ facilities of cost at most $(1.89+O(\varepsilon))\,\mathrm{opt}_k$ with probability at least $1-\varepsilon$, in time $\exp(O(\beta^{-1}\mathrm{poly}(1/\varepsilon)))\,n^{\mathrm{poly}(1/\varepsilon)}$.
--
--   A $k$-median instance $I$ has $n$ clients, $m$ facilities, rational distances and a number $k$; it is *valid* if $k\ge1$, $m\ge1$ and the distances form a pseudometric. $\mathrm{cost}(F)$ is the sum over the clients of the distance to the nearest facility of $F$, $\mathrm{opt}_\ell$ is the least cost of a nonempty set of at most $\ell$ facilities, and $I$ is *$\beta$-stable* if $k=1$ or $\mathrm{opt}_{k-1}\ge(1+\beta)\,\mathrm{opt}_k$. For natural numbers $a,b$ put
--
--   $$T_{a,b}(I,L,\varepsilon)=2^{eL}\,(|I|+2)^{e},\qquad e=a\,(\lceil 1/\varepsilon\rceil+1)^{b},$$
--
--   where $|I|$ is the length of the binary encoding of $I$.
--
--   **Statement.** There are a function $A$, natural numbers $a,b$ and a real number $C$ such that:
--
--   1. *Running time.* $A$ takes an instance $I$ (encoded by $n$, $m$, $k$ in binary and its table of distances), a natural number $L$ in unary, a rational number $\varepsilon$ in binary and a string $r$ of coin flips, and is computed by a deterministic multitape Turing machine which, for a constant $c$, halts within $c\,(T_{a,b}(I,L,\varepsilon)+\text{(length of the encoded input with the coins)}+1)$ steps and uses at most that many cells.
--   2. *Valid output.* For every valid instance with $k\le m$, every $L$, every rational $\varepsilon$ and every $r$, the output is a list of exactly $k$ distinct facilities.
--   3. *Approximation.* If moreover $0<\varepsilon<1/200$, $\beta>0$ is a real number, $I$ is $\beta$-stable and $L\ge1/\beta$, then for a uniformly random string $r$ of exactly $T_{a,b}(I,L,\varepsilon)$ coin flips,
--
--   $$\Pr_r\bigl[\mathrm{cost}(A(I,L,\varepsilon,r))\le(1.89+C\,\varepsilon)\,\mathrm{opt}_k\bigr]\;\ge\;1-\varepsilon .$$
--
--   In Part I this theorem is combined with the pseudo-approximation opening $k+O(\log n/\varepsilon^2)$ centers (Theorem 1.2 of Part I) to obtain the $1.95$-approximation for $k$-median (Theorem 1.1 of Part I). The proof gives $b=2$, $C=1000$ and an absolute constant $a$.
--
--   **Formalization Note** The machine, $c$, $a$, $b$ and $C$ do not depend on $\varepsilon$ or $\beta$; $\beta$ is not an input, only $L\ge1/\beta$. $\lceil 1/\varepsilon\rceil$ is the ceiling as a natural number ($0$ for $\varepsilon\le 0$). Probabilities are over coin strings of the stated length, of which the algorithm may read only a prefix.
-- source:
--   Buhai, Cohen-Addad, Fleischmann, Gupta, Jubés Monforte, Pittu, Stouras, Svensson, Vogl, A Better-than-2 Approximation for k-Median (Part I: arXiv:2610.18144, https://arxiv.org/abs/2610.18144; Part II: arXiv:2610.17172, https://arxiv.org/abs/2610.17172); Part II (arXiv:2610.17172), Theorem 1.1 (= Part I (arXiv:2610.18144), Theorem 1.3). Lean source: `BCFGJPSSV26.Stable.stable_main`, https://github.com/raresbuhai/formalization-of-my-research/blob/7abf511c7e99fd3fec3ff245a2b8d616ae17bc2c/BCFGJPSSV26/Stable/Main.lean#L34-L62

module

public import Definitions.Def_BCFGJPSSV26_Stable_Time_RunTime
public import Definitions.Def_BCFGJPSSV26_Combine

set_option maxSynthPendingDepth 3

@[expose] public section

namespace BCFGJPSSV26.Stable

open Encoding

theorem stable_main : Combine.Thm13 := by sorry

end BCFGJPSSV26.Stable
end
