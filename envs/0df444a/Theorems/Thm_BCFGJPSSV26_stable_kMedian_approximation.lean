-- Prove2me | Theorems.Thm_BCFGJPSSV26_stable_kMedian_approximation
-- name    : BCFGJPSSV26.stable_kMedian_approximation
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T17:47:01.511021+00:00
-- url     : https://prove2.me/theorems/3dd4f919-432c-43eb-991b-eb11361b03c0
-- title:
--   Theorem 1.3 (Part I) = Theorem 1.1 (Part II) — $(1.89+O(\varepsilon))$-approximation for stable $k$-median instances
-- statement:
--   This is Theorem 1.3 of Part I (arXiv:2610.18144), which is Theorem 1.1 of Part II (arXiv:2610.17172): on $\beta$-stable instances of $k$-median and for $\varepsilon\in(0,1/200)$, a randomized algorithm running in time $\exp(O(\beta^{-1}\mathrm{poly}(1/\varepsilon)))\,n^{\mathrm{poly}(1/\varepsilon)}$ outputs, with probability at least $1-\varepsilon$, exactly $k$ facilities of cost at most $(1.89+O(\varepsilon))\,\mathrm{opt}_k$.
--
--   **Model.** A $k$-median instance $I$ consists of $n$ clients, $m$ facilities, a number $k$ of centers to open, and rational distances between the $n+m$ points. It is *valid* if $k\ge1$, $m\ge1$ and the distances form a pseudometric (nonnegative, zero on the diagonal, symmetric, with the triangle inequality). For a nonempty set $S$ of facilities, $\mathrm{cost}(S)=\sum_{j}\min_{i\in S} d(j,i)$, the sum being over the clients $j$, and $\mathrm{opt}_\ell$ is the least cost of a nonempty set of at most $\ell$ facilities. For a real $\beta$, the instance is *$\beta$-stable* if $\mathrm{opt}_{k-1}\ge(1+\beta)\,\mathrm{opt}_k$ whenever $k\ge2$; every instance with $k=1$ is $\beta$-stable. Let $N$ be the bit length of the encoding of $I$ ($n$, $m$, $k$ in binary and the table of distances).
--
--   **Statement.** There exist constants $a,b\in\mathbb N$ and $C\in\mathbb R$ and an algorithm $A$ whose input is an instance $I$, a natural number $L$ written in unary, a rational accuracy $\varepsilon$ written in binary, and a string $r$ of coin flips, and whose output is a list of natural numbers, such that, with
--
--   $$T(I,L,\varepsilon)=2^{\,eL}\,(N+2)^{e},\qquad e=a\,\big(\lceil 1/\varepsilon\rceil+1\big)^{b},$$
--
--   the following hold.
--
--   1. **Running time.** $A$ is computed by a deterministic multitape Turing machine that, for a constant $c$, halts on every input within $c\,\big(T(I,L,\varepsilon)+|\langle I,L,\varepsilon,r\rangle|+1\big)$ steps and uses at most that many cells, where $|\langle I,L,\varepsilon,r\rangle|$ is the length of the encoded input, coins included.
--   2. **Feasibility.** For every valid instance $I$ with $k\le m$, every $L\in\mathbb N$, every rational $\varepsilon$ and every coin string $r$, the output $A(I,L,\varepsilon,r)$ is a list of exactly $k$ distinct facilities of $I$.
--   3. **Approximation.** For every valid instance $I$ with $k\le m$, every $L\in\mathbb N$ and every rational $\varepsilon$ with $0<\varepsilon<1/200$: if $I$ is $\beta$-stable for some real $\beta>0$ with $1/\beta\le L$, then, for $r$ uniformly random among the strings of exactly $T(I,L,\varepsilon)$ coin flips,
--
--   $$\Pr_r\Big[\mathrm{cost}\big(A(I,L,\varepsilon,r)\big)\ \le\ (1.89+C\,\varepsilon)\,\mathrm{opt}_k\Big]\ \ge\ 1-\varepsilon .$$
--
--   **Role.** This is the main theorem of Part II and the second ingredient of the $1.95$-approximation (Theorem 1.1 of Part I), where it is run with a fixed accuracy and with $L$ proportional to the number of extra centers of the pseudo-approximation (Theorem 1.2), so that $2^{eL}$ is polynomial in the size of the instance.
--
--   **Formalization Note** The stability parameter reaches the algorithm as a number $L\ge1/\beta$ in unary, and $\varepsilon$ is part of the input, so one algorithm and one set of constants $a$, $b$, $C$, $c$ serve all $\beta$ and $\varepsilon$; with $L=\lceil1/\beta\rceil$ and $\varepsilon\in(0,1/200)$, $T$ is the paper's $\exp(O(\beta^{-1}\mathrm{poly}(1/\varepsilon)))\,n^{\mathrm{poly}(1/\varepsilon)}$. Item 1 holds on every input, and item 2 for every $L$ and every rational $\varepsilon$, also outside $(0,1/200)$; in $T$, $\lceil1/\varepsilon\rceil$ is read as $0$ when $\varepsilon\le0$. The time bound $T$ is also the number of coins the probability is over. In the paper $\mathrm{opt}_0=\infty$, which makes every instance with $k=1$ stable; here this is part of the definition. The condition $k\le m$ ensures that $k$ distinct facilities exist; then $\mathrm{opt}_k$ is also the least cost of exactly $k$ facilities, the definition of Part II. Distances are rational, and a point that is both a client and a facility is represented by two points at distance $0$.
-- source:
--   Buhai, Cohen-Addad, Fleischmann, Gupta, Jubés Monforte, Pittu, Stouras, Svensson, Vogl, A Better-than-2 Approximation for k-Median (Part I: arXiv:2610.18144, https://arxiv.org/abs/2610.18144; Part II: arXiv:2610.17172, https://arxiv.org/abs/2610.17172); Part I (arXiv:2610.18144), Theorem 1.3; Part II (arXiv:2610.17172), Theorem 1.1. Lean source: `BCFGJPSSV26.stable_kMedian_approximation`, https://github.com/raresbuhai/formalization-of-my-research/blob/7abf511c7e99fd3fec3ff245a2b8d616ae17bc2c/BCFGJPSSV26/Solution.lean#L41-L58

module

public import Definitions.Def_BCFGJPSSV26_Model
import Definitions.Def_BCFGJPSSV26_Combine
public import Definitions.Def_BCFGJPSSV26_Greedy_PolyTime_Main
public import Definitions.Def_BCFGJPSSV26_Combine
public import Definitions.Def_BCFGJPSSV26_Stable_Time_RunTime
import Definitions.Def_BCFGJPSSV26_FL_Main

set_option maxSynthPendingDepth 3

public section

namespace BCFGJPSSV26

open Encoding

theorem stable_kMedian_approximation :
    ∃ (A : ((Instance × ℕ) × ℚ) × List Bool → List ℕ) (a b : ℕ) (C : ℝ),
      RunsInTime (encPair (encPair encInstance encUnary) encRat) encCenters A
        (stableTimeOf a b) ∧
      ∀ I : Instance, I.Valid → I.k ≤ I.m → ∀ (L : ℕ) (ε : ℚ),
        (∀ r, I.IsCenterList (A (((I, L), ε), r)) ∧ (A (((I, L), ε), r)).length = I.k) ∧
        (0 < ε → ε < 1 / 200 → ∀ β : ℝ, 0 < β → I.IsStable β → 1 / β ≤ L →
          1 - (ε : ℝ) ≤ coinProb (stableTimeOf a b ((I, L), ε))
            fun r ↦ I.cost (I.centers (A (((I, L), ε), r))) ≤
              (1.89 + C * ε) * I.opt I.k) := by sorry

end BCFGJPSSV26
end
