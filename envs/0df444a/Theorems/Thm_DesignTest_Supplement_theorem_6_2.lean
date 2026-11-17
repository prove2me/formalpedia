-- Prove2me | Theorems.Thm_DesignTest_Supplement_theorem_6_2
-- name    : DesignTest.Supplement.theorem_6_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T09:17:14.434474+00:00
-- url     : https://prove2.me/theorems/f155d9d3-f488-445f-a437-0cd46a8a82f7
-- title:
--   Theorem 6.2 — UFPE sample lower bounds under classical-description access
-- statement:
--   Throughout, $d\ge2$, $t\in\{1,\dots,d\}$ and $\delta_{\mathrm{fail}}\in(0,1/3]$ (standing assumptions of §6), $F_t(\nu)=\|M_t(\nu)\|_2^2$ is the unitary frame potential, and an estimator solves $(t,\varepsilon,\delta_{\mathrm{fail}})$-UFPE on a class of inputs if, for every $\nu$ in the class, its output $\hat F_t$ satisfies $|\hat F_t-F_t(\nu)|\le\varepsilon$ with probability at least $1-\delta_{\mathrm{fail}}$. The small-frame-potential promise (125) is $F_t(\nu)\le t!+\gamma$.
--
--   There is a universal constant $c>0$ such that every estimator in the classical-description access model making at most $m$ sample requests in every execution satisfies:
--
--   1. without a promise, for $\varepsilon\in(0,cd^{2t}]$, $m=\Omega\big(d^{4t}\varepsilon^{-2}\log(1/\delta_{\mathrm{fail}})\big)$ (126);
--   2. under the promise (125) with $\gamma\in(0,(d^{2t}-t!)/4]$ and $\varepsilon\in(0,c\gamma]$, $m=\Omega\big(d^t\gamma^{3/2}\varepsilon^{-2}\log(1/\delta_{\mathrm{fail}})\big)$ (127).
--
--   These bounds also hold in the uncontrolled and controlled unitary access models, for every processing model, regardless of the number of queries.
--
--   **Formalization Note.** A classical-description estimator is a Markov kernel from the $m$ sample matrices to $\mathbb R$.
--
--   Differences from the source:
--   - encoding: O(·) / Ω(·) with universal implicit constants → ∃ C > 0 chosen before every other parameter; reason: the theorem states the constants are universal
--   - encoding: d ≥ 2, t ∈ [d], δ_fail ∈ (0, 1/3] stated once for §6 (p.76) → explicit hypotheses of the theorem; reason: standing assumptions of the section
--   - encoding: any estimator in the classical-description access model (and, as a consequence, in every black-box model) → every Markov kernel κ from U(d)^m to ℝ; reason: samples may be drawn in advance and the descriptions determine every oracle operation (Definition 3.9, p.16), so every such estimator induces a kernel
-- source:
--   Kawachi–Nakata–Takeuchi, Testing State and Unitary Designs, STOC 2027 submission (sha256 e2f0a429…), Theorem 6.2, p.77-78 (PDF p.80-81)

import Mathlib
import Definitions.Def_DesignTest_Supplement_twirlDist

set_option autoImplicit false

namespace DesignTest.Supplement

open MeasureTheory RandomGateDesign.MasterBound

/-- **Theorem 6.2** (Sample lower bounds under classical-description access). A. Kawachi, Y. Nakata, Y. Takeuchi, *Testing State and Unitary Designs*, STOC 2027 submission (sha256 e2f0a429…), Theorem 6.2,
eqs. (126)–(127), pp.77–78.

There is a universal constant `c > 0` such that every estimator for `(t, ε, δ_fail)`-UFPE in the
classical-description access model making at most `m` sample requests in every execution satisfies:
1. without a promise, for `ε ∈ (0, c d^{2t}]`, `m = Ω(d^{4t}/ε² · log(1/δ_fail))` (126);
2. under the promise `F_t(ν) ≤ t! + γ` with `γ ∈ (0, (d^{2t} − t!)/4]` and `ε ∈ (0, cγ]`,
`m = Ω(d^t γ^{3/2}/ε² · log(1/δ_fail))` (127).
These bounds also hold in the uncontrolled and controlled unitary access models, for every processing
model, regardless of the number of queries.

**Formalization Note.** Standing assumptions of §6 (p.76): `d ≥ 2`, `t ∈ [d] = {1, …, d}`, `δ_fail ∈ (0, 1/3]`. `F_t(ν)` is `unitaryFP ν t`;
the small-frame-potential promise (125) is `F_t(ν) ≤ t! + γ`. An estimator "solves" the problem on a class of
inputs if, for every probability measure `ν` in the class, its output `F̂` satisfies `|F̂ − F_t(ν)| ≤ ε` with
probability at least `1 − δ_fail`. A classical-description estimator with at most `m` samples is a Markov kernel `κ` from `U(d)^m` to `ℝ`
(the law of the output given the sampled matrices); it simulates every black-box estimator (p.16), so the
bounds for kernels give the last sentence. `c` and the universal `Ω` constant `c'` are chosen first. -/
theorem theorem_6_2 :
    ∃ c c' : ℝ, 0 < c ∧ 0 < c' ∧ ∀ d t : ℕ, 2 ≤ d → 1 ≤ t → t ≤ d → ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 3 →
      ∀ (m : ℕ) (κ : ProbabilityTheory.Kernel (Fin m → U d) ℝ), ProbabilityTheory.IsMarkovKernel κ →
      (∀ ε : ℝ, 0 < ε → ε ≤ c * (d : ℝ) ^ (2 * t) →
        (∀ (ν : Measure (U d)) [IsProbabilityMeasure ν],
          1 - δ ≤ ∫ x, (κ x {y | |y - unitaryFP ν t| ≤ ε}).toReal ∂(Measure.pi fun _ : Fin m => ν)) →
        c' * (d : ℝ) ^ (4 * t) / ε ^ 2 * Real.log (1 / δ) ≤ (m : ℝ)) ∧
      (∀ γ ε : ℝ, 0 < γ → γ ≤ ((d : ℝ) ^ (2 * t) - (Nat.factorial t : ℝ)) / 4 → 0 < ε → ε ≤ c * γ →
        (∀ (ν : Measure (U d)) [IsProbabilityMeasure ν], unitaryFP ν t ≤ (Nat.factorial t : ℝ) + γ →
          1 - δ ≤ ∫ x, (κ x {y | |y - unitaryFP ν t| ≤ ε}).toReal ∂(Measure.pi fun _ : Fin m => ν)) →
        c' * (d : ℝ) ^ t * γ ^ ((3 : ℝ) / 2) / ε ^ 2 * Real.log (1 / δ) ≤ (m : ℝ)) := by sorry

end DesignTest.Supplement
