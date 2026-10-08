-- Prove2me | Theorems.Thm_CarryRNG_AWC_periodic_seed_iff
-- name    : CarryRNG.AWC.periodic_seed_iff
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:23:13.520274+00:00
-- url     : https://prove2.me/theorems/c64155dd-35cc-4f7c-91ee-9ed7bb792a8f
-- title:
--   p. 472, Method 3 — the seeds whose add-with-carry sequence is strictly periodic
-- statement:
--   Let $b \ge 2$ be a base, $0 < s < r$ lags, and $f$ the add-with-carry map. For a state $x = (x_1, \dots, x_r, c)$ write, following the paper, $x_r \cdots x_{s+1}$ and $x_{r-s} \cdots x_1$ for the integers whose base-$b$ representations are these strings of $r - s$ digits (most significant digit on the left):
--
--   $$
--   A = x_r \cdots x_{s+1} = \sum_{i=0}^{r-s-1} x_{s+1+i}\, b^{i}, \qquad
--   B = x_{r-s} \cdots x_1 = \sum_{i=0}^{r-s-1} x_{1+i}\, b^{i}.
--   $$
--
--   Then $x$ is a periodic point of $f$ (the sequence $x, f(x), f^2(x), \dots$ is strictly periodic, the seed itself recurring) if and only if
--
--   $$
--   \bigl(c = 0 \text{ and } A \ge B\bigr) \quad \text{or} \quad \bigl(c = 1 \text{ and } A \le B\bigr).
--   $$
--
--   This is the paper's rule for "periodic seed vectors" of the add-with-carry generator (Method 3). It holds without any primality assumption, and it includes the two trivial seeds.
--
--   **Formalization Note** In Lean, $A$ sums `x (s + i) * b ^ i` and $B$ sums `x i * b ^ i` over `i : Fin (r - s)` (Lean index $i$ is the paper's $x_{i+1}$). The worked example on p. 473, item (a), prints these two inequalities reversed; this statement follows the rule on p. 472, which is the correct one.
-- source:
--   G. Marsaglia and A. Zaman, A new class of random number generators, Ann. Appl. Probab. 1 (1991), p. 472, Section 4.5, Method 3

import Mathlib
import Definitions.Def_CarryRNG_AWC_step

namespace CarryRNG.AWC

theorem periodic_seed_iff (b : ℕ) (L : Lags) (hb : 2 ≤ b) (z : State b L.r) :
    z ∈ Function.periodicPts (step b L) ↔
      let A : ℕ := ∑ i : Fin (L.r - L.s),
        (z.x ⟨L.s + i.val, by have := i.isLt; omega⟩).val * b ^ i.val
      let B : ℕ := ∑ i : Fin (L.r - L.s),
        (z.x ⟨i.val, by have := i.isLt; have := L.hs; omega⟩).val * b ^ i.val
      (z.c = 0 ∧ B ≤ A) ∨ (z.c = 1 ∧ A ≤ B) := by sorry

end CarryRNG.AWC
