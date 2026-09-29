-- Prove2me | Theorems.Thm_BassokSubstitution_partial_derivative_formula
-- name    : BassokSubstitution.partial_derivative_formula
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T08:30:01.655454+00:00
-- url     : https://prove2.me/theorems/eb8f4bd4-01a9-4ea6-8931-d707b7f76204
-- title:
--   §2.3, Eq. (4) — the first partial derivative $\partial P/\partial y_i$
-- statement:
--   Consider the model with Assumptions 1–3 and $b \ge 0$, with independent nonnegative demands having densities and finite means, and write $\Pr$ for the joint demand law. Let $x \in \mathbb R^N$, let $y \ge 0$ and let $i$ be a product with $y_i > 0$. Then $t \mapsto P(x, y_1,\dots,y_{i-1}, t, y_{i+1},\dots,y_N)$ is differentiable at $t = y_i$, with derivative
--   $$\begin{aligned}\frac{\partial P}{\partial y_i} = {}& -c_i + s_i \Pr\{\vec S^i_{i,N} = 0\} + \sum_{k=1}^{i-1} s_k \Pr\{\vec S^k_{i,N} = 0,\ \vec S^{k+1}_{i,N} > 0\} + b\,\Pr\{S^1_i = 0,\ S^i_i > 0\}\\ &+ (T_i + b)\Pr\{S^1_i > 0\} + \sum_{k=i+1}^{N} T_k \Pr\{\vec S^1_{i,k-1} = 0,\ S^1_k > 0\}.\end{aligned}$$
--   Here $S^k_j$ is the shortage of class $j$ in the subproblem with products $k,\dots,j$, $\vec S^k_{a,n} = 0$ means $S^k_m = 0$ for all $a \le m \le n$ and $\vec S^k_{a,n} > 0$ is its negation, and $T_k = p_k + \pi_k - b$.
--
--   Each term is the value of one extra unit of product $i$ on one event: salvage of product $i$ or of a more flexible product it frees, a saved substitution cost, or extra revenue and avoided penalty for class $i$ or for a later class $k$. The formula is the basis of Theorem 1 and of the pairwise comparisons of partial derivatives in the proof of Theorem 2.
--
--   **Formalization Note.** The paper prints the two sums with "…"; their general terms are $s_k \Pr\{\vec S^k_{i,N} = 0, \vec S^{k+1}_{i,N} > 0\}$ for $k = i-1, \dots, 1$ (4b) and $T_k \Pr\{\vec S^1_{i,k-1} = 0, S^1_k > 0\}$ for $k = i+1, \dots, N$ (4d), inferred from the printed first and last terms. Indices are 0-based in Lean (class `N - 1` is the paper's $N$; the superscript $1$ is `0`). The derivative is stated with `HasDerivAt`, so its existence is part of the claim; it is claimed where $y_i > 0$, because $P$ is only defined in the model for nonnegative stock. Independence and densities are the paper's unstated hypotheses (see the Profit definition).
-- source:
--   Bassok, Anupindi, Akella, Single-Period Multiproduct Inventory Models with Substitution, Operations Research 47(4):632–642 (1999), p. 635, §2.3, Eq. (4a)–(4d)

import Mathlib
import Definitions.Def_BassokSubstitution_Profit

open MeasureTheory

namespace BassokSubstitution

/-- §2.3, Eq. (4): the partial derivative of the expected profit with respect to the stock
`y_i` of product `i` (0-based indices; superscript `k` of `S^k_j` is the first product of the
subproblem, class `N - 1` is the last class). -/
theorem partial_derivative_formula {N : ℕ} (M : Model N)
    (hA1 : M.Assumption1) (hA2 : M.Assumption2) (hA3 : M.Assumption3) (hb : 0 ≤ M.b)
    (ν : Fin N → Measure ℝ) [∀ i, IsProbabilityMeasure (ν i)] (hν : DemandLaw ν)
    (x y : Fin N → ℝ) (hy : 0 ≤ y) (i : Fin N) (hi : 0 < y i) :
    HasDerivAt (fun t : ℝ => M.profit (Measure.pi ν) x (Function.update y i t))
      (-M.c i
        + M.s i * (Measure.pi ν).real {d | ShortVecZero y d i i (N - 1)}
        + (∑ k ∈ Finset.univ.filter (fun k : Fin N => k < i),
            M.s k * (Measure.pi ν).real
              {d | ShortVecZero y d k i (N - 1) ∧ ¬ ShortVecZero y d (k + 1) i (N - 1)})
        + M.b * (Measure.pi ν).real {d | shortage y d 0 i = 0 ∧ 0 < shortage y d i i}
        + (M.T i + M.b) * (Measure.pi ν).real {d | 0 < shortage y d 0 i}
        + (∑ k ∈ Finset.univ.filter (fun k : Fin N => i < k),
            M.T k * (Measure.pi ν).real
              {d | ShortVecZero y d 0 i ((k : ℕ) - 1) ∧ 0 < shortage y d 0 k}))
      (y i) := by sorry

end BassokSubstitution
