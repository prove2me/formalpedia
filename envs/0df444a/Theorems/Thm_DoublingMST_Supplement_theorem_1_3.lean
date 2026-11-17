-- Prove2me | Theorems.Thm_DoublingMST_Supplement_theorem_1_3
-- name    : DoublingMST.Supplement.theorem_1_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T06:19:05.088398+00:00
-- url     : https://prove2.me/theorems/b0c54a38-6190-4d83-8b0f-a98c3e9eaa3b
-- title:
--   Theorem 1.3 — randomized real-RAM lower bound $\Omega\big(n\log n+\min\{n^2,\frac n\epsilon\log\frac1\epsilon\}\big)$ in doubling dimension $7$
-- statement:
--   There are absolute constants $c>0$ and $N$ such that the following holds for every $n\ge N$ and every $\epsilon\in(0,\tfrac12]$. Let $P$ be any randomized program of the real RAM with a unit-cost exact-distance oracle (Definition 2.1, with a random tape), and let $\iota$ be any assignment of $n$ distinct integer labels to the points. Suppose that on every metric $d$ on the $n$ points with doubling dimension $\mathrm{ddim}(d)\le 7$, the run of $P$ on $(\iota,\epsilon)$ with oracle $d$ halts and outputs $n-1$ label pairs forming a $(1+\epsilon)$-approximate MST with probability at least $2/3$. Then there is such a metric $d$ (with $\mathrm{ddim}(d)\le7$) on which the expected running time satisfies
--
--   $$\mathbb E[T]\ \ge\ c\Big(n\log_2 n+\min\Big\{n^2,\ \frac n\epsilon\log_2\frac1\epsilon\Big\}\Big).$$
--
--   Together with Theorem 1.1, this shows that the algorithm for doubling metrics is asymptotically optimal in its dependence on $n$ and $\epsilon$ for bounded doubling dimension.
--
--   **Formalization Note** The machine is `DoublingMST.Supplement.RMachine`; programs may use fair coins, uniform reals and arbitrary one-step integer operations, which only strengthens the lower bound. A run that never halts has running time $\infty$. The success events and running times are measurable functions of the tape.
--
--   Differences from the source:
--   - generalization: any randomized algorithm in the real RAM model of Definition 2.1 → any program of RMachine: the Definition 2.1 instructions plus fair coins, uniform reals and arbitrary one-step integer operations f : ℤ → ℤ → ℤ; reason: every randomized Definition 2.1 algorithm is such a program, so the lower bound over the richer machine implies the source's; the proof applies (after fixing the tape, reals reach control flow only through comparisons, and integers never depend on real values)
--   - generalization: worst-case expected running time over n-point metrics (labels part of the input) → for every program P fixed after n and ϵ and every fixed injective labelling ι, some metric d with ddim ≤ 7 has expected running time ≥ the bound; reason: a bad metric for every fixed labelling and program gives a bad labelled input for every algorithm; both constructions of the proof (relabeled paths, the gadget metric) use fixed labels
--   - encoding: for every sufficiently large n and 0 < ϵ ≤ 1/2, Ω(·) → ∃ c > 0, ∃ N, ∀ n ≥ N, ∀ ϵ ∈ (0, 1/2]; reason: c and N are absolute, independent of ϵ, which is what Ω with 'every sufficiently large n' means
--   - encoding: running time; returns an explicit (1+ϵ)-approximate spanning tree with probability ≥ 2/3 → haltTime ∈ ℕ∞ (⊤ for a run that never halts) integrated against tapeLaw; success event {ω | the run halts with IsApproxMST d ι ϵ out}; reason: Definition 2.1: unit cost per operation, output as n − 1 label pairs; a non-halting run has infinite running time
--   - encoding: log n, log(1/ϵ) → Real.logb 2; reason: a change of base changes only the constant c
-- source:
--   Höckendorff–Hommelsheim–Sohler–Yue, Tight Bounds for (1+ϵ)-Approximation for Minimum Spanning Trees in Doubling Metrics, STOC 2027 submission (manuscript sha256 4855d6b3…be759), Theorem 1.3, p.3 (PDF p.5); restated p.30 (PDF p.32), proof via Theorems 6.3 and 6.7

import Mathlib
import Definitions.Def_DoublingMST_Supplement_RMachine
import Definitions.Def_DoublingMST_IsMetric
import Definitions.Def_DoublingMST_ddim
import Definitions.Def_DoublingMST_IsApproxMST
open scoped Classical ENNReal

namespace DoublingMST.Supplement

open MeasureTheory

/-- **Theorem 1.3 (running-time lower bound).**
Höckendorff–Hommelsheim–Sohler–Yue, *Tight Bounds for (1+ϵ)-Approximation for Minimum Spanning
Trees in Doubling Metrics*, STOC 2027 submission (manuscript sha256 4855d6b3…be759), Theorem 1.3,
p.3 (PDF p.5), restated p.30 (PDF p.32): "For every sufficiently large integer n and
0 < ϵ ≤ 1/2, any randomized algorithm in the real RAM model with a unit-cost exact-distance oracle
of Definition 2.1 that returns an explicit (1 + ϵ)-approximate spanning tree with probability at
least 2/3 on every n-point metric of doubling dimension at most 7 has worst-case expected running
time Ω(n log n + min{n², (n/ϵ) log(1/ϵ)})."

There are `c > 0` and `N` such that for every `n ≥ N`, every `ϵ ∈ (0, 1/2]`, every randomized
program `P` and every injective labelling `ι`: if on every metric `d` on the `n` points with
`ddim d ≤ 7` the run from `(ι, ϵ)` halts with a `(1 + ϵ)`-approximate MST with probability at
least `2/3`, then some such metric has expected running time at least
`c · (n log₂ n + min{n², (n/ϵ) log₂(1/ϵ)})`.

**Formalization Note.** The program may use coins, uniform reals and arbitrary one-step integer
operations (a richer machine than Definition 2.1's, so the lower bound is stronger), and is fixed
after `n`, `ϵ` and the labels. Running time counts a non-halting run as `⊤`. Logs are base 2.
Machine conventions: `Definitions.Def_DoublingMST_Supplement_RMachine`. -/
theorem theorem_1_3 : ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ,
    ∀ n : ℕ, N ≤ n → ∀ ϵ : ℝ, 0 < ϵ → ϵ ≤ 1 / 2 →
    ∀ P : RProgram, ∀ ι : Fin n → ℤ, Function.Injective ι →
      (∀ d : Fin n → Fin n → ℝ, DoublingMST.IsMetric d → DoublingMST.ddim d ≤ 7 →
        (2 / 3 : ℝ≥0∞) ≤ tapeLaw {ω | ∃ out : List (ℤ × ℤ),
          HaltsWith P ι d ω (DoublingMST.init ι ϵ) n out ∧ DoublingMST.IsApproxMST d ι ϵ out}) →
      ∃ d : Fin n → Fin n → ℝ, DoublingMST.IsMetric d ∧ DoublingMST.ddim d ≤ 7 ∧
        ENNReal.ofReal (c * ((n : ℝ) * Real.logb 2 n +
            min ((n : ℝ) ^ 2) ((n : ℝ) / ϵ * Real.logb 2 (1 / ϵ)))) ≤
          ∫⁻ ω, ((haltTime P ι d ω (DoublingMST.init ι ϵ) : ℕ∞) : ℝ≥0∞) ∂tapeLaw := by sorry

end DoublingMST.Supplement
