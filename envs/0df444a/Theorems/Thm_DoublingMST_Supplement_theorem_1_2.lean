-- Prove2me | Theorems.Thm_DoublingMST_Supplement_theorem_1_2
-- name    : DoublingMST.Supplement.theorem_1_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T06:18:19.238898+00:00
-- url     : https://prove2.me/theorems/4fd07820-2624-43e1-ae11-28e34e6aadd3
-- title:
--   Theorem 1.2 — Euclidean $(1+\epsilon)$-MST in expected time $2^{O(d)}n\log n+O_{d,\kappa}\big(\min\{n^2,\frac{n}{\epsilon^{1-\beta_d}}\log^{1-\beta_d}\frac1\epsilon\}\big)$
-- statement:
--   Let $d\ge 1$ be the dimension and let $\beta_d=\frac{1}{\lceil d/2\rceil+1}-\kappa$. There is an absolute constant $C>0$ such that for every $d\ge 1$ and every $\kappa>0$ there are a randomized real-RAM program $P$ that uses only fair coins as randomness and a constant $C'>0$ (depending only on $d$ and $\kappa$) with the following property. For every $n\ge 2$, all distinct points $x_0,\dots,x_{n-1}\in\mathbb R^d$ given by their coordinates, and every $\epsilon\in(0,\tfrac12)$:
--
--   1. with probability $1$ over the random tape, $P$ halts and outputs $n-1$ index pairs forming a spanning tree $T$ with
--   $$\sum_{\{i,j\}\in T}\|x_i-x_j\|_2\le(1+\epsilon)\,\mathrm{MST}(X);$$
--   2. the expected number of steps is at most
--   $$2^{Cd}\,n\log_2 n+C'\min\Big\{n^2,\ \frac{n}{\epsilon^{1-\beta_d}}\,\log_2^{1-\beta_d}(1/\epsilon)\Big\}.$$
--
--   The program has no square root and no distance oracle; the approximation is measured in Euclidean lengths. For fixed $d\ge3$ this improves the $\epsilon^{-1}$ dependence of the general doubling-metric algorithm (Theorem 1.1), which is optimal for oracle access (Theorem 1.3), and shows that bound is not tight for low-dimensional Euclidean inputs.
--
--   **Formalization Note** The machine is `DoublingMST.Supplement.RMachine` (coin-only programs, Euclidean input layout); $P$ is fixed after $d$ and $\kappa$ and before $n$, $x$, $\epsilon$. Expected time is a lower Lebesgue integral of the running time in $\mathbb N_\infty$.
--
--   Differences from the source:
--   - generalization: a randomized real-RAM algorithm (Definition 2.1 with a random tape) → a coin-only program: the published Definition 2.1 instructions (integer +, −, comparisons, indirect addressing; no floor, no square root, no oracle) plus fair coins; reason: every such program is a randomized real-RAM algorithm of Definition 2.1, so the Lean existence claim specializes to the source's
--   - encoding: d ∈ Z+ a constant; 2^{O(d)}; O_{d,κ}(·) → ∃ C > 0 before dim; ∀ dim ≥ 1, ∀ κ > 0, ∃ P, ∃ C' > 0; then ∀ n, x, ϵ; reason: this is the meaning of an absolute O(d) in the exponent and of factors depending only on d and κ; the algorithm may depend on the constants d and κ
--   - reading: κ > 0 is a constant which can be made arbitrarily small → ∀ κ > 0; reason: the proof fixes any 0 < κ < 1/(⌈d/2⌉+1); a larger κ lowers β_d and only enlarges the bound (log₂(1/ϵ) > 1), so every κ > 0 is covered
--   - encoding: computes a (1+ϵ)-approximation to Euclidean MST in expected time T → almost surely over the tape the run halts with an IsApproxMST output for the Euclidean distances, and ∫⁻ haltTime d(tapeLaw) ≤ T; reason: Las Vegas reading: the subroutine of Lemma 5.1 always returns the closest pair, and the expectation is over the tape for each fixed input
--   - encoding: an n-point subset X ⊂ R^d given by coordinates → injective x : Fin n → EuclideanSpace ℝ (Fin dim), coordinates in real memory, output pairs of point indices 0..n−1, n ≥ 2; reason: Definition 2.1's Euclidean coordinate input and label-pair output; |X| ≥ 2 is the standing assumption of p.11
--   - encoding: log n, log(1/ϵ) → Real.logb 2; reason: a change of base changes only constants: 2^{C·dim} absorbs it in the first term (dim ≥ 1) and C' in the second
-- source:
--   Höckendorff–Hommelsheim–Sohler–Yue, Tight Bounds for (1+ϵ)-Approximation for Minimum Spanning Trees in Doubling Metrics, STOC 2027 submission (manuscript sha256 4855d6b3…be759), Theorem 1.2, pp.2–3 (PDF pp.4–5); restated p.28 (PDF p.30), proof pp.28–29

import Mathlib
import Definitions.Def_DoublingMST_Supplement_RMachine
import Definitions.Def_DoublingMST_IsApproxMST
open scoped Classical ENNReal

namespace DoublingMST.Supplement

open MeasureTheory

/-- **Theorem 1.2 (low-dimensional Euclidean (1 + ϵ)-MST, expected time).**
Höckendorff–Hommelsheim–Sohler–Yue, *Tight Bounds for (1+ϵ)-Approximation for Minimum Spanning
Trees in Doubling Metrics*, STOC 2027 submission (manuscript sha256 4855d6b3…be759), Theorem 1.2,
pp.2–3 (PDF pp.4–5), restated p.28 (PDF p.30): "Let d ∈ Z+ be a constant and ϵ ∈ (0, 1/2). There
is a real-RAM algorithm that, given the coordinates of an n-point subset X ⊂ R^d, computes a
(1 + ϵ)-approximation to Euclidean MST in expected time
2^{O(d)} n log n + O_{d,κ}(min{n², (n/ϵ^{1−β_d}) log^{1−β_d}(1/ϵ)}), for β_d = 1/(⌈d/2⌉+1) − κ,
where κ > 0 is a constant which can be made arbitrarily small, and O_{d,κ}(·) hides factors that
depend only on d and κ."

There is an absolute `C > 0` such that for every dimension `dim ≥ 1` and every `κ > 0` there are
a coin-only randomized program `P` and `C' > 0` such that for every `n ≥ 2`, every `n` distinct
points `x i ∈ ℝ^dim` and every `ϵ ∈ (0, 1/2)`: almost surely over the tape the run from the
Euclidean layout halts and outputs `n − 1` index pairs forming a spanning tree of Euclidean weight
at most `(1 + ϵ) · MST`, and the expected number of steps is at most
`2^{C·dim} n log₂ n + C' · min{n², (n/ϵ^{1−β}) (log₂(1/ϵ))^{1−β}}`, `β = 1/(⌈dim/2⌉+1) − κ`.

**Formalization Note.** `P` is fixed after `dim` and `κ`, before `n`, `x` and `ϵ`; it has no
oracle, no square root and no `unif`/`intOp` instructions (`CoinOnly`). The weight is the sum of
Euclidean lengths `‖x i − x j‖₂`. Logs are base 2. Machine conventions:
`Definitions.Def_DoublingMST_Supplement_RMachine`. -/
theorem theorem_1_2 : ∃ C : ℝ, 0 < C ∧
    ∀ dim : ℕ, 1 ≤ dim → ∀ κ : ℝ, 0 < κ →
    ∃ P : RProgram, CoinOnly P ∧ ∃ C' : ℝ, 0 < C' ∧
    ∀ n : ℕ, 2 ≤ n → ∀ x : Fin n → EuclideanSpace ℝ (Fin dim), Function.Injective x →
    ∀ ϵ : ℝ, 0 < ϵ → ϵ < 1 / 2 →
      (∀ᵐ ω ∂tapeLaw, ∃ out : List (ℤ × ℤ),
          HaltsWith P noLabels noDist ω (initEuclid x ϵ) n out ∧
          DoublingMST.IsApproxMST (fun i j => dist (x i) (x j)) (fun i : Fin n => ((i : ℕ) : ℤ))
            ϵ out) ∧
      ∫⁻ ω, ((haltTime P noLabels noDist ω (initEuclid x ϵ) : ℕ∞) : ℝ≥0∞) ∂tapeLaw ≤
        ENNReal.ofReal ((2 : ℝ) ^ (C * dim) * ((n : ℝ) * Real.logb 2 n) +
          C' * min ((n : ℝ) ^ 2)
            ((n : ℝ) / ϵ ^ (1 - (1 / ((⌈(dim : ℝ) / 2⌉ : ℝ) + 1) - κ)) *
              (Real.logb 2 (1 / ϵ)) ^ (1 - (1 / ((⌈(dim : ℝ) / 2⌉ : ℝ) + 1) - κ)))) := by sorry

end DoublingMST.Supplement
