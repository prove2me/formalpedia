-- Prove2me | Theorems.Thm_ColumnRandLP_step_2_EC_7
-- name    : ColumnRandLP.step_2_EC_7
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:24:40.558564+00:00
-- url     : https://prove2.me/theorems/c208d54f-3cc1-4c66-a292-c9eebaab1bee
-- title:
--   (EC.7) — w.p. $\ge 1-\delta/2$, $\|b'-b\|_1\le\frac{mC\|A\|_{\max}}{\sqrt K}(1+\sqrt{2\log(2/\delta)})$
-- statement:
--   Let $A$ be an $m\times n$ matrix, $\xi$ a probability distribution on $[n]$, $C$ a constant and $x^{*0}\in\mathbb R^n$ with $0\le x^{*0}\le C\xi$; let $b=Ax^{*0}$. Draw $J=(j_1,\dots,j_K)$, $K\ge1$, i.i.d. from $\xi$, let $x'=\frac1K\sum_{k}\frac{x^{*0}_{j_k}}{\xi_{j_k}}e_{j_k}$ and $b'=Ax'$. Then for every $\delta\in(0,1)$, with probability at least $1-\delta/2$ over $J$,
--   $$
--   \|b'-b\|_1\le\frac{m\cdot C\cdot\|A\|_{\max}}{\sqrt K}\Big(1+\sqrt{2\log\tfrac2\delta}\Big).
--   $$
--
--   This is Step 2 of the proof of Proposition EC.3: the sparsified solution $x'$ violates the equality constraints $Ax=b$ by at most this amount in $\ell_1$.
--
--   **Formalization Note** The sample is `J : Fin K → Fin n` under `sampleMeasure ξ K`; $b'$ is `A *ᵥ xprime ξ x0 J` and $b$ is written `A *ᵥ x0`. $\|A\|_{\max}$ is `Amax A`. $\log$ is natural.
--
--   Differences from the source:
--   - generalization: x*⁰ an optimal solution of P_distr and b the right-hand side of P → any x0 with 0 ≤ x0 ≤ Cξ, and b := A x0; reason: Step 2 uses only 0 ≤ x*⁰ ≤ Cξ and Ax*⁰ = b; an optimal solution of P_distr satisfies both, so the statement specializes to the paper's
--   - encoding: the sample j₁, …, j_K drawn i.i.d. from ξ → J : Fin K → Fin n under the product measure ξ^{⊗K} (sampleMeasure); reason: the same probability space, with 0-based indices
--   - reading: K, the number of samples → 1 ≤ K; reason: the bound contains 1/√K and x′ averages K terms
--   - encoding: x*⁰_{j_k}/ξ_{j_k} for a sampled index → Lean's x / 0 = 0 at ξ_{j_k} = 0 in xprime; reason: 0 ≤ x0 ≤ Cξ forces x0_j = 0 there (the remark on p.ec8), and such an index is drawn with probability 0
--   - encoding: C a nonnegative constant (Proposition EC.3) → no separate hypothesis; reason: 0 ≤ x0 ≤ Cξ and ∑ ξ_j = 1 force C ≥ 0
--   - encoding: ‖A‖max = max_ij |A_ij| → Amax A = ⨆ i, ⨆ j, |A i j|; reason: a supremum over a finite nonempty index type is the maximum; at m = 0, where the max is undefined, it is 0
-- source:
--   Akchen–Mišić, Column-Randomized Linear Programs: Performance Guarantees and Applications, arXiv:2007.10461v5, proof of Proposition EC.3, Step 2, (EC.7), p.ec9

import Mathlib
import Definitions.Def_ColumnRandLP_Norms
import Definitions.Def_ColumnRandLP_Model

open Matrix MeasureTheory

namespace ColumnRandLP

/-- **Step 2 of the proof of Proposition EC.3, (EC.7)** (Akchen–Mišić, arXiv:2007.10461v5,
proof of Proposition EC.3, Step 2, (EC.7), p.ec9). With `x*⁰`, `x′` as in Step 1, `b = A x*⁰`
and `b′ = A x′`: for every `δ ∈ (0,1)`, with probability at least `1 − δ/2`,
`‖b′ − b‖₁ ≤ m · C · ‖A‖_max/√K · (1 + √(2 log(2/δ)))`.

**Formalization Note** The paper's `x*⁰` is an optimal solution of `P_distr`, so `A x*⁰ = b`;
Step 2 uses only `0 ≤ x*⁰ ≤ Cξ` and `b = A x*⁰`, so `x0` is any vector with `0 ≤ x0 ≤ Cξ` and
`b` is written `A *ᵥ x0`. The sample is `J : Fin K → Fin n` under `ξ^{⊗K}` (`sampleMeasure`),
`b′ = A *ᵥ xprime ξ x0 J`, `‖·‖₁ = l1Norm`, `‖A‖_max = Amax A`. `K ≥ 1`; `log` is natural. -/
theorem step_2_EC_7 {m n K : ℕ} (hK : 1 ≤ K) (A : Matrix (Fin m) (Fin n) ℝ)
    (ξ : Fin n → ℝ) (hξ0 : ∀ j, 0 ≤ ξ j) (hξ1 : ∑ j, ξ j = 1) (C : ℝ) (x0 : Fin n → ℝ)
    (hx0 : 0 ≤ x0) (hx0C : x0 ≤ C • ξ) (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    ENNReal.ofReal (1 - δ / 2) ≤
      sampleMeasure ξ K {J | l1Norm (A *ᵥ xprime ξ x0 J - A *ᵥ x0) ≤
        (m : ℝ) * C * Amax A / Real.sqrt K * (1 + Real.sqrt (2 * Real.log (2 / δ)))} := by sorry

end ColumnRandLP
