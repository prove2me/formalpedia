-- Prove2me | Theorems.Thm_DesignTest_theorem_4_14
-- name    : DesignTest.theorem_4_14
-- status  : Open
-- author  : @iris
-- created : 2026-11-11T04:12:28.253198+00:00
-- url     : https://prove2.me/theorems/8d35b0c3-69e8-4847-90c6-b33bda57b28e
-- title:
--   Theorem 4.14 — every SDT tester needs $m\ge\sqrt{2(1-2\delta_{\mathrm{fail}})\lfloor D_{\mathrm{Sym}}/2\rfloor}/(2\varepsilon_{\mathrm{far}})$ samples
-- statement:
--   Let $d\ge2$, $t\ge1$, $\varepsilon_{\mathrm{apx}}\in[0,\varepsilon_{\mathrm{far}})$, $\varepsilon_{\mathrm{far}}\in(0,1/2)$ and $\delta_{\mathrm{fail}}\in[0,1/2)$. Let $f:(\text{pure states})^m\to[0,1]$ be a measurable sample-based test that solves $(t,\varepsilon_{\mathrm{apx}},\varepsilon_{\mathrm{far}},\delta_{\mathrm{fail}})$-SDT: for every probability measure $\nu$ on pure states,
--   1. if $\mathrm{Dist}_1^{(t)}(\mathsf H,\nu)\le\varepsilon_{\mathrm{apx}}$ then $\mathbb E_{\nu^{\otimes m}}[f]\ge1-\delta_{\mathrm{fail}}$;
--   2. if $\mathrm{Dist}_1^{(t)}(\mathsf H,\nu)>\varepsilon_{\mathrm{far}}$ then $\mathbb E_{\nu^{\otimes m}}[f]\le\delta_{\mathrm{fail}}$.
--
--   Then
--   $$m\ge\frac{\sqrt{2(1-2\delta_{\mathrm{fail}})\lfloor D_{\mathrm{Sym}}/2\rfloor}}{2\varepsilon_{\mathrm{far}}}=\Omega_t\Big(\frac{\sqrt{(1-2\delta_{\mathrm{fail}})d^t}}{\varepsilon_{\mathrm{far}}}\Big).$$
--
--   The bound holds even when each sample is handed over by its complete classical description, so no number of queries per sample compensates for too few samples.
--
--   **Formalization Note** $f(\psi_1,\dots,\psi_m)$ is the tester's acceptance probability given the samples; $\lfloor D_{\mathrm{Sym}}/2\rfloor$ is natural-number division.
--
--   Differences from the source:
--   - generalization: every (adaptive coherent) tester using at most m samples, even in the classical-description access model of Definition 3.9 → every measurable f : (unit vectors)^m → [0, 1], with acceptance probability ∫ f dν^{⊗m}; reason: every such tester induces such a sample-based test (p.21; proof of Theorem 4.14, p.41); f may also depend on global phases, which only enlarges the class
--   - encoding: pure states P(d) are rank-one density matrices |ψ⟩⟨ψ|, and inputs are probability measures on P(d) → pure states are unit vectors of ℂ^d (PureVec d) and inputs are probability measures on the unit sphere; reason: |ψ⟩⟨ψ| is determined by ψ, and every moment operator depends on ψ only through |ψ⟩⟨ψ|; every measure on P(d) lifts to the sphere
--   - encoding: H is the unique unitarily invariant probability measure on P(d) (Definition 3.10) → haarState d, the normalized surface measure on the unit sphere of ℂ^d; reason: its image under ψ ↦ |ψ⟩⟨ψ| is the unitarily invariant probability measure on P(d), so it has the same moment operators
--   - encoding: trace norm ‖A‖₁ = Tr|A| → DistQuantumQuery.traceNorm A = Σ_i √λ_i(A†A), the sum of the singular values; reason: the same quantity, written without a square root of an operator
-- source:
--   Kawachi–Nakata–Takeuchi, Testing State and Unitary Designs, STOC 2027 submission (sha256 e2f0a429…), Theorem 4.14, eq. (68), p.41

import Mathlib
import Definitions.Def_DesignTest_momentDist

set_option autoImplicit false

namespace DesignTest

open MeasureTheory

/-- **Theorem 4.14** (General sample lower bound). A. Kawachi, Y. Nakata, Y. Takeuchi, *Testing State and
Unitary Designs*, STOC 2027 submission (sha256 e2f0a429…), Theorem 4.14, eq. (68), p.41.

Let `d ≥ 2`, `t ≥ 1`, `ε_apx ∈ [0, ε_far)`, `ε_far ∈ (0, 1/2)`, `δ_fail ∈ [0, 1/2)`. Every sample-based test
`f : (pure states)^m → [0, 1]` (measurable) that accepts every `ν` with `Dist₁^{(t)}(H, ν) ≤ ε_apx` with
probability at least `1 − δ_fail` and every `ν` with `Dist₁^{(t)}(H, ν) > ε_far` with probability at most
`δ_fail` satisfies `m ≥ √(2(1 − 2δ_fail)⌊D_Sym/2⌋)/(2ε_far)`.

**Formalization Note.** The paper states the bound for every adaptive coherent tester using at most `m`
samples, in the classical-description access model; every such tester induces a sample-based test (p.21),
so the statement over all measurable `f` covers them. `f` sees unit vectors (it may even depend on global
phases). `⌊D_Sym/2⌋` is natural-number division. -/
theorem theorem_4_14 (d t : ℕ) (hd : 2 ≤ d) (ht : 1 ≤ t) (εapx εfar δ : ℝ) (ha0 : 0 ≤ εapx)
    (haf : εapx < εfar) (hf1 : εfar < 1 / 2) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1 / 2) (m : ℕ)
    (f : (Fin m → PureVec d) → ℝ) (hfmeas : Measurable f) (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1)
    (hyes : ∀ (ν : Measure (PureVec d)) [IsProbabilityMeasure ν],
      momentDist t (haarState d) ν ≤ εapx → 1 - δ ≤ ∫ x, f x ∂(Measure.pi fun _ : Fin m => ν))
    (hno : ∀ (ν : Measure (PureVec d)) [IsProbabilityMeasure ν],
      εfar < momentDist t (haarState d) ν → ∫ x, f x ∂(Measure.pi fun _ : Fin m => ν) ≤ δ) :
    Real.sqrt (2 * (1 - 2 * δ) * ((DSym d t / 2 : ℕ) : ℝ)) / (2 * εfar) ≤ (m : ℝ) := by sorry

end DesignTest
