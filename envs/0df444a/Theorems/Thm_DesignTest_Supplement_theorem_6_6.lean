-- Prove2me | Theorems.Thm_DesignTest_Supplement_theorem_6_6
-- name    : DesignTest.Supplement.theorem_6_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T09:18:08.871197+00:00
-- url     : https://prove2.me/theorems/51f73535-1133-4f75-b836-d1b2b19230d0
-- title:
--   Theorem 6.6 — UFPE query lower bounds in the controlled unitary access model
-- statement:
--   Throughout, $d\ge2$, $t\in\{1,\dots,d\}$ and $\delta_{\mathrm{fail}}\in(0,1/3]$ (standing assumptions of §6), $F_t(\nu)=\|M_t(\nu)\|_2^2$ is the unitary frame potential, and an estimator solves $(t,\varepsilon,\delta_{\mathrm{fail}})$-UFPE on a class of inputs if, for every $\nu$ in the class, its output $\hat F_t$ satisfies $|\hat F_t-F_t(\nu)|\le\varepsilon$ with probability at least $1-\delta_{\mathrm{fail}}$. The small-frame-potential promise (125) is $F_t(\nu)\le t!+\gamma$.
--
--   There is a universal constant $c>0$ such that every controlled estimator (adaptive coherent, with access to $C_U$ and $C_U^\dagger$) solving UFPE with at most $q$ queries satisfies, for any number $m$ of samples:
--
--   1. without a promise, for $\varepsilon\in(0,cd^{2t}]$, $q=\Omega(d^{2t}\sqrt t/\varepsilon)$ (142);
--   2. under the promise (125) with $\gamma\in(0,(d^{2t}-t!)/4]$ and $\varepsilon\in(0,c\gamma]$, $q=\Omega(\max\{d^{t/2}\gamma^{3/4}/\varepsilon,\ \gamma\sqrt t/\varepsilon\})$ (143).
--
--   Differences from the source:
--   - encoding: O(·) / Ω(·) with universal implicit constants → ∃ C > 0 chosen before every other parameter; reason: the theorem states the constants are universal
--   - encoding: d ≥ 2, t ∈ [d], δ_fail ∈ (0, 1/3] stated once for §6 (p.76) → explicit hypotheses of the theorem; reason: standing assumptions of the section
--   - encoding: algorithms with internal randomness and quantum measurements → RandProc: arbitrary measurable seed space, finite-outcome measurements, output function of seed and transcript; reason: a continuous-outcome measurement in finite dimension is a randomization of finite-outcome ones plus post-processing (Chiribella–D'Ariano–Schlingemann 2007); finite-dimensional strategies have finite-outcome classical control
-- source:
--   Kawachi–Nakata–Takeuchi, Testing State and Unitary Designs, STOC 2027 submission (sha256 e2f0a429…), Theorem 6.6, p.88 (PDF p.91)

import Mathlib
import Definitions.Def_DesignTest_Supplement_CAC

set_option autoImplicit false

namespace DesignTest.Supplement

open MeasureTheory RandomGateDesign.MasterBound

/-- **Theorem 6.6** (Query lower bounds in the controlled unitary access model). A. Kawachi, Y. Nakata, Y. Takeuchi, *Testing State and Unitary Designs*, STOC 2027 submission (sha256 e2f0a429…), Theorem 6.6,
eqs. (142)–(143), p.88.

Let `δ_fail ∈ (0, 1/3]`. There is a universal constant `c > 0` such that every controlled estimator solving
`(t, ε, δ_fail)`-UFPE with `q` queries satisfies:
1. without a promise, for `ε ∈ (0, c d^{2t}]`, `q = Ω(d^{2t} √t/ε)` (142);
2. under the promise (125), for `γ ∈ (0, (d^{2t} − t!)/4]` and `ε ∈ (0, cγ]`,
`q = Ω(max{d^{t/2} γ^{3/4}/ε, γ √t/ε})` (143).
These bounds hold for any number `m` of unitary samples.

**Formalization Note.** Standing assumptions of §6 (p.76): `d ≥ 2`, `t ∈ [d] = {1, …, d}`, `δ_fail ∈ (0, 1/3]`. `F_t(ν)` is `unitaryFP ν t`;
the small-frame-potential promise (125) is `F_t(ν) ≤ t! + γ`. An estimator "solves" the problem on a class of
inputs if, for every probability measure `ν` in the class, its output `F̂` satisfies `|F̂ − F_t(ν)| ≤ ε` with
probability at least `1 − δ_fail`. A controlled estimator is an adaptive coherent algorithm with access to `C_U` and `C_U†`
(`CACProc d m q w K J`, the most general class, p.16); `q` bounds its calls in every execution. `c` and the
universal `Ω` constant `c'` are chosen first; `m`, the workspace and instrument sizes are arbitrary. -/
theorem theorem_6_6 :
    ∃ c c' : ℝ, 0 < c ∧ 0 < c' ∧ ∀ d t : ℕ, 2 ≤ d → 1 ≤ t → t ≤ d → ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 3 →
      ∀ (m q w K J : ℕ) (T : CACProc d m q w K J),
      (∀ ε : ℝ, 0 < ε → ε ≤ c * (d : ℝ) ^ (2 * t) →
        (∀ (ν : Measure (U d)) [IsProbabilityMeasure ν], 1 - δ ≤ T.successProb ν (unitaryFP ν t) ε) →
        c' * ((d : ℝ) ^ (2 * t) * Real.sqrt (t : ℝ) / ε) ≤ (q : ℝ)) ∧
      (∀ γ ε : ℝ, 0 < γ → γ ≤ ((d : ℝ) ^ (2 * t) - (Nat.factorial t : ℝ)) / 4 → 0 < ε → ε ≤ c * γ →
        (∀ (ν : Measure (U d)) [IsProbabilityMeasure ν], unitaryFP ν t ≤ (Nat.factorial t : ℝ) + γ → 1 - δ ≤ T.successProb ν (unitaryFP ν t) ε) →
        c' * (max ((d : ℝ) ^ ((t : ℝ) / 2) * γ ^ ((3 : ℝ) / 4) / ε) (γ * Real.sqrt (t : ℝ) / ε)) ≤ (q : ℝ)) := by sorry

end DesignTest.Supplement
