-- Prove2me | Theorems.Thm_ExactDFTRefine_Main_theorem_1_1
-- name    : ExactDFTRefine.Main.theorem_1_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T04:02:16.089925+00:00
-- url     : https://prove2.me/theorems/857e58c0-b8aa-4fab-a169-d8e89b3e5017
-- title:
--   Theorem 1.1 — exact length-n DFT for every n ≥ 1 in O(n (log n)^{1−δ}) RAM work, δ = 30201659/10^10
-- statement:
--   Let $\delta = 30201659/10^{10} = 0.0030201659$. In the exact complex-arithmetic RAM model of Section 2 (definition `RAM`) there are two fixed deterministic programs, a root-order program $P_1$ and a transform program $P_2$, and constants $c \in \mathbb N$, $K > 0$, $n_0$ such that for every integer $n \ge 1$ and every $x \in \mathbb C^n$:
--
--   - $P_1$ on input $n$ halts with a root order $D(n)$, a natural number with $1 \le D(n) < 1024n^3$;
--   - one supplied-root operation provides $\zeta_{D(n)} = \exp(2\pi i/D(n))$;
--   - $P_2$ on $(n, D(n), \zeta_{D(n)}, x)$ halts with output $\mathrm{DFT}_n x$, where $(\mathrm{DFT}_n x)_j = \sum_{k=0}^{n-1}\zeta_n^{jk}x_k$, $0 \le j < n$;
--   - every integer value and address occurring in the run of either program is at most $(n+2)^c$ in absolute value;
--   - the total work $W(n)$ (both programs, the root primitive, scalar preparation, array and index operations, each instruction one unit) satisfies, for $n \ge n_0$,
--   $$W(n) \le K\, n\, (\log n)^{1-\delta},$$
--   with the natural logarithm and $(\log n)^{1-\delta}$ a real power.
--
--   Correctness holds for every $n \ge 1$; only the work bound is asymptotic. The theorem improves the earlier certified saving $C_0 = 0.00302016$ of Kartal's instantiation of Sussman's construction by $5.9\times 10^{-9}$.
--
--   Differences from the source:
--   - encoding: W(n) = O(n(log n)^{1−δ}) → ∃ K > 0, n₀, ∀ n ≥ n₀, ∀ x, W ≤ K n (log n)^{1−δ}; reason: standard reading of O; W(n) is the worst case over inputs; correctness is required for every n ≥ 1
--   - reading: the exact complex-arithmetic RAM model of Section 2 (a summary of OpenAI's reference specification [11], not reproduced in the paper) → the machine `Instr`/`step` of `ExactDFTRefine_Main_RAM`: integer registers and integer array memory with literal, +, −, ×, Euclidean division and remainder, loads and stores, jumps on = and <; complex scalar registers and array memory with Gaussian-rational literals, integer-to-scalar conversion, exact +, −, ×, ÷ (stuck on division by 0), loads and stores; halt; no instruction from scalars to integers or control; reason: the paper states only the model's clauses; this is the minimal machine with every capability Section 2 names and none that would trivialize the bound (no scalar comparison, rounding or conversion to integers, no transform, convolution or product instruction)
--   - encoding: work counts exact arithmetic and RAM operations, both programs and the root primitive → W = (instructions executed by P₁, including halt) + 1 (root primitive) + (instructions executed by P₂, including halt), each instruction one unit; reason: unit-cost RAM semantics
--   - encoding: a fixed program computes D(n) from n; the root primitive supplies ζ_{D(n)}; a second fixed program computes (1) → P₁ starts with ireg 0 = n and halts with ireg 0 = D; P₂ starts with ireg 0 = n, ireg 1 = D, creg 0 = exp(2πi/D), cmem k = x_k (0 ≤ k < n), all else 0, and halts with cmem j = (DFT_n x)_j (0 ≤ j < n); reason: input/output layout of the run; any fixed layout is interconvertible in O(n) work
--   - encoding: integer values and addresses bounded by a fixed polynomial in n, (n + 2)^c for one constant c → ∃ c : ℕ, at every step of both programs every integer register and integer memory cell has absolute value ≤ (n + 2)^c (addresses are integer-register values); reason: Section 2's form of the bound
-- source:
--   Yao, Liu, A Numerical Refinement of an Exact Discrete Fourier Transform Bound, arXiv:2611.01257v1, p. 2, Theorem 1.1 (model: p. 2, §2)

import Mathlib
import Definitions.Def_ExactDFTRefine_Main_RAM
import Definitions.Def_ExactDFTRefine_Main_Moments

namespace ExactDFTRefine.Main

/-- **Theorem 1.1**, p. 2. In the exact complex-arithmetic RAM model of Section 2 there are fixed
deterministic programs (a root-order program and a transform program) and a constant `c` such
that for every `n ≥ 1` and every `x ∈ ℂ^n` the run computes `DFT_n x` with `1 ≤ D(n) < 1024 n^3`,
one supplied root, all integer values and addresses at most `(n + 2)^c`, and total work
`W(n) = O(n (log n)^{1-δ})`, `δ = 30201659/10^10`. -/
theorem theorem_1_1 :
    ∃ (P₁ P₂ : Program) (c : ℕ) (K : ℝ) (n₀ : ℕ), 0 < K ∧
      ∀ n : ℕ, 1 ≤ n → ∀ x : Fin n → ℂ, ∃ W : ℕ, DFTRun P₁ P₂ c n x W ∧
        (n₀ ≤ n → (W : ℝ) ≤ K * n * Real.log (n : ℝ) ^ (1 - delta)) := by sorry

end ExactDFTRefine.Main
