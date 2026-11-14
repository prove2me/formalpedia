-- Prove2me | Theorems.Thm_BCFGJPSSV26_Greedy_greedy_main
-- name    : BCFGJPSSV26.Greedy.greedy_main
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T17:43:28.929755+00:00
-- url     : https://prove2.me/theorems/46331fc7-7c03-4e73-8599-0a8107ffd4e2
-- title:
--   Theorem 1.2 (Part I) — $(1.9499+\varepsilon)$-approximation for k-median with $k+O(\log n/\varepsilon^2)$ centers
-- statement:
--   This is Theorem 1.2 of Part I (Theorem 5.16 in full): a deterministic polynomial-time pseudo-approximation for k-median that opens $k+O(\log n/\varepsilon^2)$ centers of cost at most $(1.9499+\varepsilon)$ times the optimum with $k$ centers.
--
--   A k-median instance $I$ consists of $n$ clients, $m$ facilities, a number $k$, and rational distances $d$ between all $n+m$ points. It is *valid* if $k\ge 1$, $m\ge 1$ and $d$ is a pseudometric (nonnegative, zero on the diagonal, symmetric, satisfying the triangle inequality). For a nonempty set $S$ of facilities, $\mathrm{cost}(S)=\sum_{j}\min_{i\in S}d(j,i)$, the sum over the clients, and $\mathrm{opt}_k$ is the least cost of a nonempty set of at most $k$ facilities.
--
--   **Statement.** There is a constant $C\in\mathbb{R}$ such that for every real $\varepsilon>0$ there is an algorithm $A$, computable in polynomial time, such that for every valid instance $I$:
--
--   1. $A(I)$ is a nonempty list of facilities of $I$ without repetitions;
--   2. the number of facilities satisfies
--
--   $$\lvert A(I)\rvert\;\le\;k+\frac{C\,\ln n}{\varepsilon^{2}};$$
--
--   3. $\mathrm{cost}(A(I))\le(1.9499+\varepsilon)\,\mathrm{opt}_k$.
--
--   Here $n$ is the number of clients and $\ln$ is the natural logarithm. The constant $C$ does not depend on $\varepsilon$ or on the instance; the algorithm $A$ depends on $\varepsilon$.
--
--   Theorem 1.2 is one of the two ingredients of the $1.95$-approximation for k-median (Theorem 1.1): it is run with fewer centers, and combined with the algorithm for stable instances (Theorem 1.3, proved in Part II), which handles the case where removing a few centers raises the optimum.
--
--   **Formalization Note** “Computable in polynomial time” means: computed by a deterministic multitape Turing machine with a binary alphabet, in time and space bounded by polynomially bounded functions of the length of the encoded instance ($n$, $m$, $k$ in binary and the table of the rational distances); the output is the list of facility indices in binary. The proof gives $C=10^{10}$; the statement only asserts that some $C$ exists. With the convention $\ln 0=0$, for $n\le 1$ the output has at most $k$ facilities.
-- source:
--   Buhai, Cohen-Addad, Fleischmann, Gupta, Jubés Monforte, Pittu, Stouras, Svensson, Vogl, A Better-than-2 Approximation for k-Median (Part I: arXiv:2610.18144, https://arxiv.org/abs/2610.18144; Part II: arXiv:2610.17172, https://arxiv.org/abs/2610.17172); Part I (arXiv:2610.18144), Theorem 1.2 (Theorem 5.16 in full). Lean source: `BCFGJPSSV26.Greedy.greedy_main`, https://github.com/raresbuhai/formalization-of-my-research/blob/7abf511c7e99fd3fec3ff245a2b8d616ae17bc2c/BCFGJPSSV26/Greedy/Main.lean#L24-L27

module

public import Definitions.Def_BCFGJPSSV26_Greedy_PolyTime_Main
public import Definitions.Def_BCFGJPSSV26_Combine

set_option maxSynthPendingDepth 3

@[expose] public section

namespace BCFGJPSSV26.Greedy

theorem greedy_main : Combine.Thm12 := by sorry

end BCFGJPSSV26.Greedy
end
