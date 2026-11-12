-- Prove2me | Theorems.Thm_FasterWCTFPTAS_Main_theorem_1_1
-- name    : FasterWCTFPTAS.Main.theorem_1_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T07:08:10.140547+00:00
-- url     : https://prove2.me/theorems/56b097bb-159a-49d3-942c-f28c68066de7
-- title:
--   Theorem 1.1 — an FPTAS for Pm||Σw_jC_j in time O(n(n/ε)^{(m−1)/2+α}), and O(n√(n/ε)) for m = 2
-- statement:
--   Fix a number of machines $m\ge2$.
--
--   1. For every constant $\alpha>0$ there are an admissible program $P$ and a constant $C>0$ such that for every instance with $n\ge1$ jobs, processing times $p_j>0$ and weights $w_j\ge0$, and every $\varepsilon\in(0,1]$, the program $P$ run on $[\varepsilon,p_1,\dots,p_n,w_1,\dots,w_n]$ halts within
--   $$
--   C\cdot n\cdot\Big(\frac n\varepsilon\Big)^{(m-1)/2+\alpha}
--   $$
--   steps and outputs an assignment $\sigma$ of the jobs to the machines such that, with every machine processing its jobs in Smith's order,
--   $$
--   \mathrm{cost}(\sigma)\le(1+\varepsilon)\cdot\mathrm{OPT}.
--   $$
--   2. If $m=2$, there are an admissible program and a constant $C>0$ with the same guarantee within $C\cdot n\cdot\sqrt{n/\varepsilon}$ steps.
--
--   $\mathrm{OPT}$ is the minimum of $\sum_jw_jC_j$ over all nonpreemptive schedules. The jobs are given in arbitrary order. This improves Sahni's $O(n(n/\varepsilon)^{m-1})$ FPTAS of 1976.
--
--   **Formalization Note** Each program and its constant are fixed before the instance and depend only on $m$ (and $\alpha$); $m$ is not part of the input. The output is the list of machine indices $\sigma(j)\in\{0,\dots,m-1\}$, and its cost is evaluated with Smith's order on every machine (non-increasing $w_j/p_j$, ties by index), which is the paper's "increasing index" order on the sorted instance. Without the running-time clause the statement would be trivial (exhaustive search over the $m^n$ assignments is exact).
--
--   Differences from the source:
--   - reading: running time in O(·), machine model not named → number of executed instructions of an admissible program of the deterministic unit-cost real RAM of FasterWCTFPTAS.Main.Machine (rational literals, exact + − × ÷, comparisons, indirect addressing, work-bounded floor); reason: the source names no machine; this model supports the cited real-arithmetic constructions and excludes bit tricks that would trivialize the bound
--   - reading: O(·) bounds with a fixed constant → ∃ C > 0 chosen together with the program, before n, p, w and ε; it may depend only on the fixed m and α; reason: standard meaning of O(·) for a fixed dimension and constant α
--   - reading: "for any ε > 0" (FPTAS, p. 1) → ε ∈ (0, 1]; reason: for ε → ∞ the bound C·n(n/ε)^{(m−1)/2+α} tends to 0 while writing the n output entries takes n steps, so the literal reading is undefined for large ε; (0, 1] is the standard FPTAS range and the proof requires δ = ε/n < 1
--   - encoding: n jobs → n ≥ 1; reason: at n = 0 the bound is 0 and no program halts in 0 steps; the empty instance is excluded only
--   - encoding: a schedule S = (S_1, …, S_m) of the sorted instance, processed in increasing index order; OPT ≔ min_S cost(S) → an output assignment σ on the instance as given (unsorted), costed with Smith's order on every machine; OPT the minimum over all nonpreemptive schedules; reason: the paper sorts without loss of generality; on the sorted instance Smith's order is the increasing-index order and both optima agree by Smith's rule
--   - generalization: §4 restatement: integer processing times and weights → real p_j > 0, w_j ≥ 0 (as in the problem statement of §1, p. 1); reason: integer instances are a special case; the p. 1 statement of Theorem 1.1 is for real data
-- source:
--   Karl Bringmann, Anita Dürr, Karol Węgrzycki, STOC 2027 submission #1072 (October 2026), p. 11 (PDF p. 12), Theorem 1.1 (also stated p. 1 (PDF p. 2), proved p. 16 (PDF p. 17))

import Mathlib
import Definitions.Def_FasterWCTFPTAS_Main_Machine
import Definitions.Def_FasterWCTFPTAS_Main_Encoding
import Definitions.Def_FasterWCTFPTAS_Main_Scheduling

set_option autoImplicit false

namespace FasterWCTFPTAS.Main

/-- Theorem 1.1, p. 11 (PDF 12; also p. 1 and p. 16). For every fixed `m ≥ 2`:
(1) for every constant `α > 0` there are an admissible program `P` and a constant `C > 0` such that
for every instance of `Pm||Σ w_j C_j` with `n ≥ 1` jobs, real `p_j > 0`, `w_j ≥ 0`, and
every `ε ∈ (0, 1]`, `P` halts on `[ε, p, w]` within `C · n · (n/ε)^{(m−1)/2+α}` steps and outputs an
assignment `σ` whose cost with Smith's order on every machine is at most `(1 + ε) · OPT`;
(2) if `m = 2`, the same holds with a program and constant for the bound `C · n · √(n/ε)`. -/
theorem theorem_1_1 (m : ℕ) (hm : 2 ≤ m) :
    (∀ α : ℝ, 0 < α →
      ∃ P : Machine.Program, Machine.Admissible P ∧ ∃ C : ℝ, 0 < C ∧
        ∀ (n : ℕ), 1 ≤ n → ∀ (p w : Fin n → ℝ), (∀ j, 0 < p j) → (∀ j, 0 ≤ w j) →
        ∀ (ε : ℝ), 0 < ε → ε ≤ 1 →
          ∃ σ : Fin n → Fin m,
            Machine.output P (schedInput ε p w) = some (assignmentOutput σ) ∧
            Machine.HaltsWithin P (schedInput ε p w)
              (C * n * ((n : ℝ) / ε) ^ (((m : ℝ) - 1) / 2 + α)) ∧
            smithCost p w σ ≤ (1 + ε) * OPT m p w) ∧
    (m = 2 →
      ∃ P : Machine.Program, Machine.Admissible P ∧ ∃ C : ℝ, 0 < C ∧
        ∀ (n : ℕ), 1 ≤ n → ∀ (p w : Fin n → ℝ), (∀ j, 0 < p j) → (∀ j, 0 ≤ w j) →
        ∀ (ε : ℝ), 0 < ε → ε ≤ 1 →
          ∃ σ : Fin n → Fin m,
            Machine.output P (schedInput ε p w) = some (assignmentOutput σ) ∧
            Machine.HaltsWithin P (schedInput ε p w) (C * n * Real.sqrt ((n : ℝ) / ε)) ∧
            smithCost p w σ ≤ (1 + ε) * OPT m p w) := by sorry

end FasterWCTFPTAS.Main
