-- Prove2me | Theorems.Thm_BCFGJPSSV26_kMedian_pseudoApproximation
-- name    : BCFGJPSSV26.kMedian_pseudoApproximation
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T17:46:58.085641+00:00
-- url     : https://prove2.me/theorems/24a37f82-c7af-48af-924a-580253415201
-- title:
--   Theorem 1.2 (Part I) — pseudo-approximation for $k$-median with $k+O(\log n/\varepsilon^2)$ centers
-- statement:
--   This is Theorem 1.2 of Part I (arXiv:2610.18144; Theorem 5.16 in the full version): for every $\varepsilon>0$ there is a polynomial-time algorithm for $k$-median that opens at most $k+O(\log n/\varepsilon^2)$ centers, of cost at most $(1.9499+\varepsilon)$ times the optimum with $k$ centers.
--
--   **Model.** A $k$-median instance $I$ consists of $n$ clients, $m$ facilities, a number $k$ of centers to open, and rational distances between the $n+m$ points. It is *valid* if $k\ge1$, $m\ge1$ and the distances form a pseudometric (nonnegative, zero on the diagonal, symmetric, with the triangle inequality). For a nonempty set $S$ of facilities, $\mathrm{cost}(S)=\sum_{j}\min_{i\in S} d(j,i)$, the sum being over the clients $j$, and $\mathrm{opt}_\ell$ is the least cost of a nonempty set of at most $\ell$ facilities. An algorithm is *polynomial-time* if a deterministic multitape Turing machine computes it within time and space polynomially bounded in the length of the encoded instance ($n$, $m$, $k$ in binary and the table of distances).
--
--   **Statement.** There is a constant $C\in\mathbb R$ such that for every real $\varepsilon>0$ there is a deterministic polynomial-time algorithm $A_\varepsilon$, mapping instances to lists of natural numbers, such that for every valid instance $I$ the output $S=A_\varepsilon(I)$ satisfies:
--
--   1. $S$ is a nonempty list of distinct facilities of $I$;
--   2. the number of facilities and their cost are bounded by
--
--   $$|S|\ \le\ k+\frac{C\,\ln n}{\varepsilon^{2}}\qquad\text{and}\qquad\mathrm{cost}(S)\ \le\ (1.9499+\varepsilon)\,\mathrm{opt}_k .$$
--
--   Here $n$ is the number of clients of $I$ and $\ln$ is the natural logarithm. The constant $C$ is the same for all $\varepsilon$ and all instances; the algorithm and its polynomial may depend on $\varepsilon$.
--
--   **Role.** This is one of the two ingredients of the $1.95$-approximation (Theorem 1.1), where it is used with $\varepsilon=10^{-5}$; the other is the algorithm for stable instances (Theorem 1.3). The algorithm is the log-adaptive greedy algorithm of Part I, Section 5, with the bids $[\alpha-1.224\,d]^+$, and the factor $1.9499$ comes from the bound on the factor-revealing program (Theorem 4.4).
--
--   **Formalization Note** Instances have rational distances, and a point that is both a client and a facility is represented by two points at distance $0$. An instance may have no client; then $\ln n$ is read as $0$. Theorem 5.16 of the paper is stated for small $\varepsilon$ with the factor $(1+\varepsilon)\,1.9499$; rescaling $\varepsilon$ changes only $C$, and for large $\varepsilon$ a constant-factor approximation with $k$ centers (local search) serves.
-- source:
--   Buhai, Cohen-Addad, Fleischmann, Gupta, Jubés Monforte, Pittu, Stouras, Svensson, Vogl, A Better-than-2 Approximation for k-Median (Part I: arXiv:2610.18144, https://arxiv.org/abs/2610.18144; Part II: arXiv:2610.17172, https://arxiv.org/abs/2610.17172); Part I (arXiv:2610.18144), Theorem 1.2 (Theorem 5.16 in full). Lean source: `BCFGJPSSV26.kMedian_pseudoApproximation`, https://github.com/raresbuhai/formalization-of-my-research/blob/7abf511c7e99fd3fec3ff245a2b8d616ae17bc2c/BCFGJPSSV26/Solution.lean#L30-L39

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

theorem kMedian_pseudoApproximation :
    ∃ C : ℝ, ∀ ε : ℝ, 0 < ε →
      ∃ A : Instance → List ℕ, Turing.MultiTapeTM.ComputableInPolyTime A encInstance encCenters ∧
        ∀ I : Instance, I.Valid →
          I.IsCenterList (A I) ∧ ((A I).length : ℝ) ≤ I.k + C * Real.log I.n / ε ^ 2 ∧
          I.cost (I.centers (A I)) ≤ (1.9499 + ε) * I.opt I.k := by sorry

end BCFGJPSSV26
end
