-- Prove2me | Theorems.Thm_DermanSeqDecisions_LinProg_lemma_linear_fractional
-- name    : DermanSeqDecisions.LinProg.lemma_linear_fractional
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T10:43:34.381289+00:00
-- url     : https://prove2.me/theorems/4ee9ab11-6aba-458f-b2c1-4158ae7ca951
-- title:
--   Lemma (pp. 22–23): a linear-fractional program reduces to a linear program
-- statement:
--   Let $g(x) = \dfrac{\sum_i c_i x_i}{\sum_i d_i x_i}$ and consider the constraints
--   $$\text{(11)} \qquad x_i \ge 0, \qquad \sum_i a_{ji} x_i = b_j \quad (j = 1, \dots, m).$$
--   Assume
--
--   (i) $\sum_i a_{ji} x_i = 0$ for all $j$ and $x \ge 0$ imply $x = 0$;
--
--   (ii) every $x$ satisfying (11) has $\sum_i d_i x_i > 0$.
--
--   Let (12) be the constraints $z_i \ge 0$ ($i = 1, \dots, n+1$), $\sum_i a_{ji} z_i - b_j z_{n+1} = 0$, $\sum_i d_i z_i = 1$, and $h(z) = \sum_i c_i z_i$. Then:
--
--   1. every $(z, z_{n+1})$ satisfying (12) has $z_{n+1} > 0$;
--   2. the map $x \mapsto \big(x / \sum_i d_i x_i,\ 1 / \sum_i d_i x_i\big)$ sends (11) into (12) with $h(z) = g(x)$;
--   3. the map $(z, z_{n+1}) \mapsto z / z_{n+1}$ sends (12) into (11) with $g(x) = h(z)$, and the two maps are mutually inverse;
--   4. consequently, if $(z, z_{n+1})$ minimizes $h$ subject to (12), then $x = z/z_{n+1}$ minimizes $g$ subject to (11).
--
--   This is the step that turns Problem 2's ratio objective (9) into a linear program.
--
--   **Formalization Note.** Variables and constraints are indexed by arbitrary types (a finite one for the variables). Two misprints of the page are corrected: in (11) the sum runs over $i$, not $j$, and in (i) the indices run over $i = 1, \dots, n$, not from $0$.
-- source:
--   Derman, On Sequential Decisions and Markov Chains, Management Science 9(1):16–24 (1962), DOI 10.1287/mnsc.9.1.16, pp. 22–23, §3, Lemma and its proof, (11) and (12)

import Mathlib
import Definitions.Def_DermanSeqDecisions_LinProg_LinearFractional

namespace DermanSeqDecisions.LinProg

/-- Lemma, pp. 22–23 (Derman, *On Sequential Decisions and Markov Chains*, Management Science 9(1):16–24 (1962), DOI 10.1287/mnsc.9.1.16, §3, Lemma, with its proof's transformation and the program (12)).

Let `c, d` be real vectors indexed by the variables `i`, `A = (a_{ji})` and `b = (b_j)` real data
indexed by the constraints `j`. Assume
(i) `∑_i a_{ji} x_i = 0` for all `j` and `x ≥ 0` imply `x = 0`, and
(ii) every `x` satisfying (11) has `∑_i d_i x_i > 0`.
Then:
1. every `(z, z_{n+1})` satisfying (12) has `z_{n+1} > 0`;
2. `x ↦ (x / ∑_i d_i x_i, 1 / ∑_i d_i x_i)` maps (11) into (12) with `h(z) = g(x)`;
3. `(z, z_{n+1}) ↦ z / z_{n+1}` maps (12) into (11) with `g(x) = h(z)`, and the two maps are mutually
   inverse (the transformation is one-to-one between (11) and (12));
4. hence, for every minimizer `(z, z_{n+1})` of `h` subject to (12), `x = z / z_{n+1}` minimizes `g`
   subject to (11).

**Formalization Note.** Variables range over a finite type `ι` and constraints over a type `κ`
(`Fin n`, `Fin m` in the paper). Two misprints are corrected: (11) prints `∑_{j=1}^n a_{ji} x_i`
(the sum is over `i`), and (i) prints `∑_{i=0}^n` and `i = 0, ⋯, n` (read `i = 1, ⋯, n`). -/
theorem lemma_linear_fractional {ι κ : Type*} [Fintype ι]
    (A : κ → ι → ℝ) (b : κ → ℝ) (c d : ι → ℝ)
    (hi : ∀ x : ι → ℝ, (∀ i, 0 ≤ x i) → (∀ j, ∑ i, A j i * x i = 0) → ∀ i, x i = 0)
    (hii : ∀ x : ι → ℝ, IsFeasible11 A b x → 0 < ∑ i, d i * x i) :
    (∀ (z : ι → ℝ) (zlast : ℝ), IsFeasible12 A b d z zlast → 0 < zlast) ∧
    (∀ x : ι → ℝ, IsFeasible11 A b x →
      IsFeasible12 A b d (fun i => x i / ∑ i', d i' * x i') (1 / ∑ i', d i' * x i') ∧
      linObj c (fun i => x i / ∑ i', d i' * x i') = fracObj c d x) ∧
    (∀ (z : ι → ℝ) (zlast : ℝ), IsFeasible12 A b d z zlast →
      IsFeasible11 A b (fun i => z i / zlast) ∧ fracObj c d (fun i => z i / zlast) = linObj c z ∧
      (fun i => z i / zlast / ∑ i', d i' * (z i' / zlast)) = z ∧
      1 / ∑ i', d i' * (z i' / zlast) = zlast) ∧
    (∀ x : ι → ℝ, IsFeasible11 A b x →
      (fun i => (x i / ∑ i', d i' * x i') / (1 / ∑ i', d i' * x i')) = x) ∧
    (∀ (z : ι → ℝ) (zlast : ℝ), IsFeasible12 A b d z zlast →
      (∀ (z' : ι → ℝ) (zlast' : ℝ), IsFeasible12 A b d z' zlast' → linObj c z ≤ linObj c z') →
      IsFeasible11 A b (fun i => z i / zlast) ∧
      ∀ x' : ι → ℝ, IsFeasible11 A b x' → fracObj c d (fun i => z i / zlast) ≤ fracObj c d x') := by sorry

end DermanSeqDecisions.LinProg
