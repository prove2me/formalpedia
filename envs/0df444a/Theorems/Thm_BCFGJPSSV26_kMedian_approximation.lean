-- Prove2me | Theorems.Thm_BCFGJPSSV26_kMedian_approximation
-- name    : BCFGJPSSV26.kMedian_approximation
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T17:44:17.691502+00:00
-- url     : https://prove2.me/theorems/200f44e0-5095-4924-9a98-2797674abd73
-- title:
--   Theorem 1.1 (Part I) — a randomized polynomial-time $1.95$-approximation for $k$-median
-- statement:
--   This is Theorem 1.1 of Part I (arXiv:2610.18144), the main result of the paper: there is a randomized polynomial-time $1.95$-approximation algorithm for $k$-median.
--
--   **Model.** A $k$-median instance $I$ consists of $n$ clients, $m$ facilities, a number $k$ of centers to open, and rational distances between the $n+m$ points. It is *valid* if $k\ge1$, $m\ge1$ and the distances form a pseudometric (nonnegative, zero on the diagonal, symmetric, with the triangle inequality). For a nonempty set $S$ of facilities, $\mathrm{cost}(S)=\sum_{j}\min_{i\in S} d(j,i)$, the sum being over the clients $j$, and $\mathrm{opt}_\ell$ is the least cost of a nonempty set of at most $\ell$ facilities. Let $N$ be the bit length of the encoding of $I$ ($n$, $m$, $k$ in binary and the table of distances).
--
--   **Statement.** There exist an exponent $e\in\mathbb N$ and an algorithm $A$ that takes an instance $I$ and a string $r$ of coin flips and returns a list of natural numbers, such that the following hold.
--
--   1. **Running time.** $A$ is computed by a deterministic multitape Turing machine that, for a constant $c$, halts on every input $(I,r)$ within $c\,\big((N+2)^{e}+|\langle I,r\rangle|+1\big)$ steps and uses at most that many cells, where $|\langle I,r\rangle|$ is the length of the encoded input, coins included.
--   2. **Feasibility.** For every valid instance $I$ and every coin string $r$, the output $A(I,r)$ is a nonempty list of distinct facilities of $I$, of length at most $k$.
--   3. **Approximation.** For every valid instance $I$, for $r$ uniformly random among the strings of exactly $(N+2)^{e}$ coin flips,
--
--   $$\Pr_r\Big[\mathrm{cost}\big(A(I,r)\big)\ \le\ 1.95\cdot\mathrm{opt}_k\Big]\ \ge\ \frac23 .$$
--
--   **Role.** This is the headline theorem. It is derived from the pseudo-approximation opening $k+O(\log n/\varepsilon^2)$ centers (Theorem 1.2) and the $(1.89+O(\varepsilon))$-approximation for stable instances (Theorem 1.3) by the combination argument of Part I, Section 1.1, step (ii).
--
--   **Formalization Note** Distances are rational, and a point that is both a client and a facility is represented by two points at distance $0$. Polynomial time is measured on multitape Turing machines in the bit length $N$ of the instance, so it is polynomial in $n+m$ and in the bits of the distances. The time bound $(N+2)^e$ is also the number of coins the probability is over. The paper does not fix the success probability; here it is $2/3$, and any constant can be raised by repetition, keeping the cheapest output. Item 2 holds for all coin strings, not only with high probability.
-- source:
--   Buhai, Cohen-Addad, Fleischmann, Gupta, Jubés Monforte, Pittu, Stouras, Svensson, Vogl, A Better-than-2 Approximation for k-Median (Part I: arXiv:2610.18144, https://arxiv.org/abs/2610.18144; Part II: arXiv:2610.17172, https://arxiv.org/abs/2610.17172); Part I (arXiv:2610.18144), Theorem 1.1. Lean source: `BCFGJPSSV26.kMedian_approximation`, https://github.com/raresbuhai/formalization-of-my-research/blob/7abf511c7e99fd3fec3ff245a2b8d616ae17bc2c/BCFGJPSSV26/Solution.lean#L60-L70

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

theorem kMedian_approximation :
    ∃ (A : Instance × List Bool → List ℕ) (e : ℕ),
      RunsInTime encInstance encCenters A (fun I ↦ ((encInstance I).length + 2) ^ e) ∧
      ∀ I : Instance, I.Valid →
        (∀ r, I.IsCenterList (A (I, r)) ∧ (A (I, r)).length ≤ I.k) ∧
        2 / 3 ≤ coinProb (((encInstance I).length + 2) ^ e)
          fun r ↦ I.cost (I.centers (A (I, r))) ≤ 1.95 * I.opt I.k := by sorry

end BCFGJPSSV26
end
