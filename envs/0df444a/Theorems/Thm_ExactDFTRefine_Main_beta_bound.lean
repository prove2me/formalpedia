-- Prove2me | Theorems.Thm_ExactDFTRefine_Main_beta_bound
-- name    : ExactDFTRefine.Main.beta_bound
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T04:02:04.718769+00:00
-- url     : https://prove2.me/theorems/2b9172bd-b0b2-45f1-b764-5198b556c96f
-- title:
--   Proof of Theorem 1.1 — δ < β < C, and W(n) = O(n (log n)^{1−β} (log log n)^2) with β = 3020165925/10^12
-- statement:
--   Let $\beta = 3020165925/10^{12}$, $\delta = 30201659/10^{10}$ and $C = 60403319/20000000000$. Then $\delta < \beta < C$, and in the exact complex-arithmetic RAM model (definition `RAM`) there are fixed programs $P_1$ (root order) and $P_2$ (transform), a constant $c \in \mathbb N$, $K > 0$ and $n_0$ such that for every $n \ge 1$ and every $x \in \mathbb C^n$ the run of $(P_1, P_2)$ on $(n, x)$ computes $\mathrm{DFT}_n x$ with $1 \le D(n) < 1024n^3$, one supplied root, every integer value and address at most $(n+2)^c$, and work $W$ satisfying, for $n \ge n_0$,
--   $$W \le K\, n\, (\log n)^{1-\beta} (\log\log n)^2.$$
--   Logarithms are natural. This is the bound the Fourier reduction gives at kernel exponent $1-\beta$; it is stronger than Theorem 1.1, whose exponent saving $\delta$ is smaller than $\beta$.
--
--   Differences from the source:
--   - reading: with kernel exponent 1 − β, the Fourier reduction, including its preparation costs, gives W(n) = O(n(log n)^{1−β}(log log n)^2) → existence of fixed programs computing the DFT for every n ≥ 1 in the model of Section 2 with that work bound and the root-order and integer clauses of Theorem 1.1; reason: the reduction is cited, not stated; its output is the transform algorithm whose fixed-program, root-order and integer bounds the paper says the same reduction supplies
--   - encoding: W(n) = O(f(n)) → ∃ K > 0, n₀, ∀ n ≥ n₀, ∀ x, W ≤ K f(n); reason: standard reading of O; W(n) is the worst case over inputs
--   - reading: the exact complex-arithmetic RAM model of Section 2 (a summary of OpenAI's reference specification [11], not reproduced in the paper) → the machine `Instr`/`step` of `ExactDFTRefine_Main_RAM`: integer registers and integer array memory with literal, +, −, ×, Euclidean division and remainder, loads and stores, jumps on = and <; complex scalar registers and array memory with Gaussian-rational literals, integer-to-scalar conversion, exact +, −, ×, ÷ (stuck on division by 0), loads and stores; halt; no instruction from scalars to integers or control; reason: the paper states only the model's clauses; this is the minimal machine with every capability Section 2 names and none that would trivialize the bound (no scalar comparison, rounding or conversion to integers, no transform, convolution or product instruction)
--   - encoding: work counts exact arithmetic and RAM operations, both programs and the root primitive → W = (instructions executed by P₁, including halt) + 1 (root primitive) + (instructions executed by P₂, including halt), each instruction one unit; reason: unit-cost RAM semantics
--   - encoding: a fixed program computes D(n) from n; the root primitive supplies ζ_{D(n)}; a second fixed program computes (1) → P₁ starts with ireg 0 = n and halts with ireg 0 = D; P₂ starts with ireg 0 = n, ireg 1 = D, creg 0 = exp(2πi/D), cmem k = x_k (0 ≤ k < n), all else 0, and halts with cmem j = (DFT_n x)_j (0 ≤ j < n); reason: input/output layout of the run; any fixed layout is interconvertible in O(n) work
--   - encoding: integer values and addresses bounded by a fixed polynomial in n, (n + 2)^c for one constant c → ∃ c : ℕ, at every step of both programs every integer register and integer memory cell has absolute value ≤ (n + 2)^c (addresses are integer-register values); reason: Section 2's form of the bound
-- source:
--   Yao, Liu, A Numerical Refinement of an Exact Discrete Fourier Transform Bound, arXiv:2611.01257v1, p. 6, proof of Theorem 1.1 (choice of β and the bound W(n) = O(n(log n)^{1−β}(log log n)^2))

import Mathlib
import Definitions.Def_ExactDFTRefine_Main_RAM
import Definitions.Def_ExactDFTRefine_Main_Moments

namespace ExactDFTRefine.Main

/-- **Proof of Theorem 1.1, the intermediate saving `β`**, p. 6. `δ < β < C` for
`β = 3020165925/10^12`, and there are fixed programs of the exact complex-arithmetic RAM computing
the length-`n` DFT for every `n ≥ 1` with `W(n) = O(n (log n)^{1-β} (log log n)^2)`. -/
theorem beta_bound :
    delta < beta ∧ beta < Cpar ∧
    ∃ (P₁ P₂ : Program) (c : ℕ) (K : ℝ) (n₀ : ℕ), 0 < K ∧
      ∀ n : ℕ, 1 ≤ n → ∀ x : Fin n → ℂ, ∃ W : ℕ, DFTRun P₁ P₂ c n x W ∧
        (n₀ ≤ n → (W : ℝ) ≤
          K * n * Real.log (n : ℝ) ^ (1 - beta) * Real.log (Real.log (n : ℝ)) ^ 2) := by sorry

end ExactDFTRefine.Main
