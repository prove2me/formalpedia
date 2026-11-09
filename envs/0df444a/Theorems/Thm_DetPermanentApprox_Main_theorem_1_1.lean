-- Prove2me | Theorems.Thm_DetPermanentApprox_Main_theorem_1_1
-- name    : DetPermanentApprox.Main.theorem_1_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:26:01.547276+00:00
-- url     : https://prove2.me/theorems/4eb01576-ee29-48d1-b85a-ab8d9c905acb
-- title:
--   Theorem 1.1 — Deterministic strongly polynomial permanent approximation
-- statement:
--   For every fixed real $0<\varepsilon\le1$, a single deterministic finite arithmetic program works for every dimension $n\ge0$ and every entrywise nonnegative real matrix $A$. Its nonnegative output $Q$ satisfies
--
--   $$\operatorname{per}A\le Q\le(1+\varepsilon)^n\operatorname{per}A.$$
--
--   There is an absolute constant $c>0$, chosen before $\varepsilon$, for which the execution uses at most $\max(2,n)^{c\varepsilon^{-2}\log^3(2/\varepsilon)}$ unit-cost instructions. For rational matrices, every rational register and memory value in that same execution has reduced binary bit length bounded by a polynomial in the total input length; the polynomial may depend on the fixed precision. All divisions have nonzero denominators. The zero permanent and empty matrix are included. This is the full strongly polynomial upper-estimate guarantee, not only a numerical existence assertion.
--
--   Differences from the source:
--   - encoding: finite labelled matrix, graph, and coordinate sets → Fin n or arbitrary finite types with explicit row and column copies; reason: finite enumerations and reindexing preserve every source instance
--   - encoding: permanent summed over row-to-column permutations → Mathlib matrix permanent with the inverse permutation convention; reason: reindexing the finite sum by permutation inversion gives exactly the source value
--   - encoding: arithmetic operations and comparisons with polynomial rational intermediate bit lengths → finite rational-literal real pointer programs, guarded divisions, explicit input/output layouts, and bounds on actual runs and traces; reason: each executed instruction has unit cost and no elementary-function or counting oracle is present; polynomial control overhead is absorbed in the source asymptotic bounds
--   - encoding: the asymptotic operation bound stated in n with separate small base cases → max(2,n) in the global operation bound; reason: the bound for n at least two is unchanged and the n=0,1 executions have a finite uniform budget
-- source:
--   Vishesh Jain, Dingding Dong, STOC 2027 submission #704 (October 2026), Theorem 1.1, p. 1 (PDF p. 1); computational model §1.1, p. 2 (PDF p. 2); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/704.pdf

import Mathlib
import Definitions.Def_DetPermanentApprox_Main_Computation

namespace DetPermanentApprox.Main

/-- Vishesh Jain, Dingding Dong, STOC 2027 submission #704 (October 2026),
Theorem 1.1, p.1 (PDF p.1), and the strong-polynomial definition in §1.1, p.2.
An absolute exponent constant precedes the precision parameter; the finite program
and rational trace polynomial precede every input dimension and matrix. -/
theorem theorem_1_1 :
    ∃ c : ℝ, 0 < c ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ∃ P : Program, RationalProgram P ∧
        (∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ),
          (∀ i j, 0 ≤ A i j) →
          ∃ T : ℕ, validRun P (matrixInput A) T ∧
            (T : ℝ) ≤ (max 2 (n : ℝ)) ^ (c * ε⁻¹ ^ 2 * Real.log (2 / ε) ^ 3) ∧
            0 ≤ output P (matrixInput A) T ∧
            A.permanent ≤ output P (matrixInput A) T ∧
            output P (matrixInput A) T ≤ (1 + ε) ^ n * A.permanent) ∧
        (∃ b d : ℕ, 0 < b ∧
          ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℚ),
            (∀ i j, 0 ≤ A i j) →
            ∃ T : ℕ,
              validRun P (matrixInput (fun i j => (A i j : ℝ))) T ∧
              traceBound P (rationalMatrixInput A) T
                (b * (inputLength (rationalMatrixInput A) + 1) ^ d)) := by sorry

end DetPermanentApprox.Main
