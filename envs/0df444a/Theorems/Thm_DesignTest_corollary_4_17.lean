-- Prove2me | Theorems.Thm_DesignTest_corollary_4_17
-- name    : DesignTest.corollary_4_17
-- status  : Open
-- author  : @iris
-- created : 2026-11-11T04:13:08.901873+00:00
-- url     : https://prove2.me/theorems/f5e97f18-3829-4e38-a5b9-33da2e03ae5e
-- title:
--   Corollary 4.17 — inverse-square sample lower bounds for $t=1$ (every $d\ge2$, constant 128) and $t=2$ (prime-power $d$, constant 256)
-- statement:
--   Let $\varepsilon_{\mathrm{apx}}\in[0,\varepsilon_{\mathrm{far}})$, $\varepsilon_{\mathrm{far}}\in(0,1/4]$ and $\delta_{\mathrm{fail}}\in[0,1/2)$. Every measurable sample-based test $f:(\text{pure states})^m\to[0,1]$ that solves $(t,\varepsilon_{\mathrm{apx}},\varepsilon_{\mathrm{far}},\delta_{\mathrm{fail}})$-SDT (accepts every $\nu$ with $\mathrm{Dist}_1^{(t)}(\mathsf H,\nu)\le\varepsilon_{\mathrm{apx}}$ with probability $\ge1-\delta_{\mathrm{fail}}$, and every $\nu$ with $\mathrm{Dist}_1^{(t)}(\mathsf H,\nu)>\varepsilon_{\mathrm{far}}$ with probability $\le\delta_{\mathrm{fail}}$) satisfies
--   $$t=1:\quad m\ge\frac{(1-2\delta_{\mathrm{fail}})\sqrt d}{128\,\varepsilon_{\mathrm{far}}^2}\quad\text{for every }d\ge2,$$
--   $$t=2:\quad m\ge\frac{(1-2\delta_{\mathrm{fail}})\sqrt{d(d+1)/2}}{256\,\varepsilon_{\mathrm{far}}^2}\quad\text{for every prime-power }d\ge2 .$$
--
--   For $t=1,2$ this matches the upper bound of Theorem 4.11 in both $d$ and $\varepsilon_{\mathrm{far}}$, for fixed failure probability.
--
--   **Formalization Note** As in Theorem 4.14, $f$ is the tester's acceptance probability given the $m$ samples.
--
--   Differences from the source:
--   - generalization: every (adaptive coherent) tester using at most m samples, even in the classical-description access model of Definition 3.9 → every measurable f : (unit vectors)^m → [0, 1], with acceptance probability ∫ f dν^{⊗m}; reason: every such tester induces such a sample-based test (p.21; proof of Theorem 4.14, p.41); f may also depend on global phases, which only enlarges the class
--   - encoding: pure states P(d) are rank-one density matrices |ψ⟩⟨ψ|, and inputs are probability measures on P(d) → pure states are unit vectors of ℂ^d (PureVec d) and inputs are probability measures on the unit sphere; reason: |ψ⟩⟨ψ| is determined by ψ, and every moment operator depends on ψ only through |ψ⟩⟨ψ|; every measure on P(d) lifts to the sphere
--   - encoding: H is the unique unitarily invariant probability measure on P(d) (Definition 3.10) → haarState d, the normalized surface measure on the unit sphere of ℂ^d; reason: its image under ψ ↦ |ψ⟩⟨ψ| is the unitarily invariant probability measure on P(d), so it has the same moment operators
--   - encoding: trace norm ‖A‖₁ = Tr|A| → DistQuantumQuery.traceNorm A = Σ_i √λ_i(A†A), the sum of the singular values; reason: the same quantity, written without a square root of an operator
-- source:
--   Kawachi–Nakata–Takeuchi, Testing State and Unitary Designs, STOC 2027 submission (sha256 e2f0a429…), Corollary 4.17, eq. (74), p.44

import Mathlib
import Definitions.Def_DesignTest_momentDist

set_option autoImplicit false

namespace DesignTest

open MeasureTheory

/-- **Corollary 4.17** (Inverse-square bounds for `t = 1, 2`). A. Kawachi, Y. Nakata, Y. Takeuchi, *Testing
State and Unitary Designs*, STOC 2027 submission (sha256 e2f0a429…), Corollary 4.17, eq. (74), p.44.

For `ε_apx ∈ [0, ε_far)`, `ε_far ∈ (0, 1/4]`, `δ_fail ∈ [0, 1/2)`, every measurable sample-based test
`f : (pure states)^m → [0, 1]` that solves `(t, ε_apx, ε_far, δ_fail)`-SDT satisfies
1. `t = 1`: `m ≥ (1 − 2δ_fail)√d/(128 ε_far²)` for every `d ≥ 2`;
2. `t = 2`: `m ≥ (1 − 2δ_fail)√(d(d + 1)/2)/(256 ε_far²)` for every prime-power `d ≥ 2`.

**Formalization Note.** As in `theorem_4_14`, "every tester that uses at most `m` samples, in the
classical-description access model" is represented by every measurable `f` into `[0, 1]` (p.21). -/
theorem corollary_4_17 :
    (∀ d : ℕ, 2 ≤ d → ∀ εapx εfar δ : ℝ, 0 ≤ εapx → εapx < εfar → εfar ≤ 1 / 4 → 0 ≤ δ → δ < 1 / 2 →
      ∀ (m : ℕ) (f : (Fin m → PureVec d) → ℝ), Measurable f → (∀ x, 0 ≤ f x ∧ f x ≤ 1) →
      (∀ (ν : Measure (PureVec d)) [IsProbabilityMeasure ν],
        momentDist 1 (haarState d) ν ≤ εapx → 1 - δ ≤ ∫ x, f x ∂(Measure.pi fun _ : Fin m => ν)) →
      (∀ (ν : Measure (PureVec d)) [IsProbabilityMeasure ν],
        εfar < momentDist 1 (haarState d) ν → ∫ x, f x ∂(Measure.pi fun _ : Fin m => ν) ≤ δ) →
      (1 - 2 * δ) * Real.sqrt (d : ℝ) / (128 * εfar ^ 2) ≤ (m : ℝ)) ∧
    (∀ d : ℕ, 2 ≤ d → IsPrimePow d → ∀ εapx εfar δ : ℝ, 0 ≤ εapx → εapx < εfar → εfar ≤ 1 / 4 →
      0 ≤ δ → δ < 1 / 2 →
      ∀ (m : ℕ) (f : (Fin m → PureVec d) → ℝ), Measurable f → (∀ x, 0 ≤ f x ∧ f x ≤ 1) →
      (∀ (ν : Measure (PureVec d)) [IsProbabilityMeasure ν],
        momentDist 2 (haarState d) ν ≤ εapx → 1 - δ ≤ ∫ x, f x ∂(Measure.pi fun _ : Fin m => ν)) →
      (∀ (ν : Measure (PureVec d)) [IsProbabilityMeasure ν],
        εfar < momentDist 2 (haarState d) ν → ∫ x, f x ∂(Measure.pi fun _ : Fin m => ν) ≤ δ) →
      (1 - 2 * δ) * Real.sqrt ((d : ℝ) * ((d : ℝ) + 1) / 2) / (256 * εfar ^ 2) ≤ (m : ℝ)) := by sorry

end DesignTest
