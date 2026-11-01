-- Prove2me | Theorems.Thm_ColumnRandLP_step_1_EC_5
-- name    : ColumnRandLP.step_1_EC_5
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:24:52.741447+00:00
-- url     : https://prove2.me/theorems/b0e410ad-d90d-40e5-958b-f34e13cffe72
-- title:
--   (EC.5) — w.p. $\ge 1-\delta/2$, $\|x'-x^{*0}\|_2\le\frac{C}{\sqrt K}(1+\sqrt{2\log(2/\delta)})$
-- statement:
--   Let $\xi$ be a probability distribution on $[n]$, $C$ a constant and $x^{*0}\in\mathbb R^n$ with $0\le x^{*0}\le C\xi$. Draw $J=(j_1,\dots,j_K)$, $K\ge1$, i.i.d. from $\xi$ and set
--   $$
--   x'=\frac1K\sum_{k=1}^K\frac{x^{*0}_{j_k}}{\xi_{j_k}}\,e_{j_k}.
--   $$
--   Then for every $\delta\in(0,1)$, with probability at least $1-\delta/2$ over $J$,
--   $$
--   \|x'-x^{*0}\|_2\le\frac{C}{\sqrt K}\Big(1+\sqrt{2\log\tfrac2\delta}\Big).
--   $$
--
--   This is Step 1 of the proof of Proposition EC.3: the importance-weighted sparsification $x'$, which uses only sampled columns, is close to the optimal solution $x^{*0}$ of the distributional counterpart.
--
--   **Formalization Note** The sample is `J : Fin K → Fin n` under the product law `sampleMeasure ξ K`; $x'$ is `xprime ξ x0 J`. Lean's $x/0=0$ is harmless because $0\le x^{*0}\le C\xi$ forces $x^{*0}_j=0$ when $\xi_j=0$. $C\ge0$ is implied by the hypotheses. $\log$ is natural.
--
--   Differences from the source:
--   - generalization: x*⁰ an optimal solution of P_distr → any x0 with 0 ≤ x0 ≤ Cξ; reason: Step 1 uses only these constraints of (5c); an optimal solution of P_distr satisfies them, so the statement specializes to the paper's
--   - encoding: the sample j₁, …, j_K drawn i.i.d. from ξ → J : Fin K → Fin n under the product measure ξ^{⊗K} (sampleMeasure); reason: the same probability space, with 0-based indices
--   - reading: K, the number of samples → 1 ≤ K; reason: the bound contains 1/√K and x′ averages K terms
--   - encoding: x*⁰_{j_k}/ξ_{j_k} for a sampled index → Lean's x / 0 = 0 at ξ_{j_k} = 0 in xprime; reason: 0 ≤ x0 ≤ Cξ forces x0_j = 0 there (the remark on p.ec8), and such an index is drawn with probability 0
--   - encoding: C a nonnegative constant (Proposition EC.3) → no separate hypothesis; reason: 0 ≤ x0 ≤ Cξ and ∑ ξ_j = 1 force C ≥ 0
-- source:
--   Akchen–Mišić, Column-Randomized Linear Programs: Performance Guarantees and Applications, arXiv:2007.10461v5, proof of Proposition EC.3, Step 1, (EC.5), p.ec8

import Mathlib
import Definitions.Def_ColumnRandLP_Norms
import Definitions.Def_ColumnRandLP_Model

open MeasureTheory

namespace ColumnRandLP

/-- **Step 1 of the proof of Proposition EC.3, (EC.5)** (Akchen–Mišić, arXiv:2007.10461v5,
proof of Proposition EC.3, Step 1, (EC.5), p.ec8). Let `x*⁰` satisfy `0 ≤ x*⁰ ≤ C·ξ` and let
`x′ = (1/K) ∑_k (x*⁰_{j_k}/ξ_{j_k}) e_{j_k}` for the sample `J = (j₁, …, j_K)` drawn i.i.d. from
`ξ`. For every `δ ∈ (0,1)`, with probability at least `1 − δ/2`,
`‖x′ − x*⁰‖₂ ≤ C/√K · (1 + √(2 log(2/δ)))`.

**Formalization Note** The paper's `x*⁰` is an optimal solution of `P_distr`; Step 1 uses only
`0 ≤ x*⁰ ≤ Cξ`, so `x0` is any such vector. The sample is `J : Fin K → Fin n` under the product
measure `ξ^{⊗K}` (`sampleMeasure`), with `ξ ≥ 0`, `∑ ξ = 1`; `x′` is `xprime ξ x0 J`. `K ≥ 1`;
`log` is natural. `C ≥ 0` is not assumed separately: it follows from `0 ≤ x0 ≤ Cξ` and `∑ ξ = 1`. -/
theorem step_1_EC_5 {n K : ℕ} (hK : 1 ≤ K) (ξ : Fin n → ℝ) (hξ0 : ∀ j, 0 ≤ ξ j)
    (hξ1 : ∑ j, ξ j = 1) (C : ℝ) (x0 : Fin n → ℝ) (hx0 : 0 ≤ x0) (hx0C : x0 ≤ C • ξ)
    (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    ENNReal.ofReal (1 - δ / 2) ≤
      sampleMeasure ξ K {J | l2Norm (xprime ξ x0 J - x0) ≤
        C / Real.sqrt K * (1 + Real.sqrt (2 * Real.log (2 / δ)))} := by sorry

end ColumnRandLP
