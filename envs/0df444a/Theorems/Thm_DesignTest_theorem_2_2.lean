-- Prove2me | Theorems.Thm_DesignTest_theorem_2_2
-- name    : DesignTest.theorem_2_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-11T04:13:23.728955+00:00
-- url     : https://prove2.me/theorems/3e62c843-a04a-4dfe-93a5-d365b39d5761
-- title:
--   Theorem 2.2 — exact state $t$-design testing has sample complexity $\Theta_t(d^{t/2})$: Theorems 4.11, 4.14 and Corollary 4.17
-- statement:
--   This is the formal content of Theorem 2.2, the conjunction of its three formal versions. Pure states are unit vectors of $\mathbb C^d$, inputs are probability measures $\nu$ on them, $\mathsf H$ is the Haar state measure, $\mathrm{Dist}_1^{(t)}(\mathsf H,\nu)=\frac12\|M_t(\mathsf H)-M_t(\nu)\|_1$ and $D_{\mathrm{Sym}}=\binom{d+t-1}t$.
--
--   1. **Upper bound (Theorem 4.11).** There is a universal $C>0$ such that for every $d\ge2$, $t\ge1$, $\varepsilon_{\mathrm{far}}\in(0,1]$ and $\delta_{\mathrm{fail}}\in(0,1/2)$ some non-adaptive coherent tester with $m$ samples and $q$ queries per sample,
--   $$m\le C\frac{\sqrt{D_{\mathrm{Sym}}}}{\varepsilon_{\mathrm{far}}^2}\log\frac1{\delta_{\mathrm{fail}}},\quad q\le C\frac{tD_{\mathrm{Sym}}^{3/2}}{\varepsilon_{\mathrm{far}}^2},\quad mq\le C\frac{tD_{\mathrm{Sym}}^2}{\varepsilon_{\mathrm{far}}^4}\log\frac1{\delta_{\mathrm{fail}}},$$
--   accepts every exact state $t$-design with probability $\ge1-\delta_{\mathrm{fail}}$ and every $\nu$ with $\mathrm{Dist}_1^{(t)}(\mathsf H,\nu)>\varepsilon_{\mathrm{far}}$ with probability $\le\delta_{\mathrm{fail}}$.
--   2. **General lower bound (Theorem 4.14).** For $d\ge2$, $t\ge1$, $\varepsilon_{\mathrm{apx}}\in[0,\varepsilon_{\mathrm{far}})$, $\varepsilon_{\mathrm{far}}\in(0,1/2)$, $\delta_{\mathrm{fail}}\in[0,1/2)$, every measurable sample-based test $f:(\text{pure states})^m\to[0,1]$ solving $(t,\varepsilon_{\mathrm{apx}},\varepsilon_{\mathrm{far}},\delta_{\mathrm{fail}})$-SDT has
--   $$m\ge\frac{\sqrt{2(1-2\delta_{\mathrm{fail}})\lfloor D_{\mathrm{Sym}}/2\rfloor}}{2\varepsilon_{\mathrm{far}}}.$$
--   3. **Inverse-square bounds (Corollary 4.17).** For $\varepsilon_{\mathrm{apx}}\in[0,\varepsilon_{\mathrm{far}})$, $\varepsilon_{\mathrm{far}}\in(0,1/4]$, $\delta_{\mathrm{fail}}\in[0,1/2)$, every such test has $m\ge(1-2\delta_{\mathrm{fail}})\sqrt d/(128\varepsilon_{\mathrm{far}}^2)$ for $t=1$ and every $d\ge2$, and $m\ge(1-2\delta_{\mathrm{fail}})\sqrt{d(d+1)/2}/(256\varepsilon_{\mathrm{far}}^2)$ for $t=2$ and every prime-power $d\ge2$.
--
--   Since $d^t/t!\le D_{\mathrm{Sym}}\le(d+t-1)^t/t!$, the sample complexity of exact state $t$-design testing is $\Theta_t(d^{t/2})$ for constant $\varepsilon_{\mathrm{far}}$, and $\Theta(d^{t/2}/\varepsilon_{\mathrm{far}}^2)$ for $t=1$ and for $t=2$ in prime-power dimensions; the lower bounds hold even when every sample is given by its complete classical description.
--
--   **Formalization Note** A non-adaptive coherent tester is a POVM effect on the $mq$ supplied copies; a sample-based test is the acceptance probability of a tester as a function of the samples.
--
--   Differences from the source:
--   - generalization: informal statement: m = O_t(d^{t/2}/ε_far²), q = O_t(d^{3t/2}/ε_far²), m = Ω_t(d^{t/2}/ε_far), Ω(d^{t/2}/ε_far²) for t = 1, 2, at a fixed constant δ_fail → the formal Theorems 4.11, 4.14 and Corollary 4.17 with their explicit constants, the log(1/δ_fail) factor and every δ_fail in their ranges; reason: Theorem 2.2 names these formal results; the asymptotic forms follow from d^t/t! ≤ D_Sym ≤ (d + t − 1)^t/t! (p.19)
--   - generalization: every (adaptive coherent) tester using at most m samples, even in the classical-description access model of Definition 3.9 → every measurable f : (unit vectors)^m → [0, 1], with acceptance probability ∫ f dν^{⊗m}; reason: every such tester induces such a sample-based test (p.21; proof of Theorem 4.14, p.41); f may also depend on global phases, which only enlarges the class
--   - encoding: pure states P(d) are rank-one density matrices |ψ⟩⟨ψ|, and inputs are probability measures on P(d) → pure states are unit vectors of ℂ^d (PureVec d) and inputs are probability measures on the unit sphere; reason: |ψ⟩⟨ψ| is determined by ψ, and every moment operator depends on ψ only through |ψ⟩⟨ψ|; every measure on P(d) lifts to the sphere
--   - encoding: H is the unique unitarily invariant probability measure on P(d) (Definition 3.10) → haarState d, the normalized surface measure on the unit sphere of ℂ^d; reason: its image under ψ ↦ |ψ⟩⟨ψ| is the unitarily invariant probability measure on P(d), so it has the same moment operators
--   - encoding: trace norm ‖A‖₁ = Tr|A| → DistQuantumQuery.traceNorm A = Σ_i √λ_i(A†A), the sum of the singular values; reason: the same quantity, written without a square root of an operator
--   - encoding: m = O(√D_Sym/ε_far² · log(1/δ_fail)), q = O(t D_Sym^{3/2}/ε_far²), q_total = O(t D_Sym²/ε_far⁴ · log(1/δ_fail)) → one constant C > 0 chosen before d, t, ε_far, δ_fail with m ≤ C√D_Sym/ε_far²·log(1/δ), q ≤ C t D_Sym^{3/2}/ε_far², m q ≤ C t D_Sym²/ε_far⁴·log(1/δ); reason: the O(·) of (56)–(58) hide an absolute constant (the t-dependence is explicit)
--   - encoding: a non-adaptive coherent tester in the state-preparation access model (Definitions 3.3, 3.5, 3.6) → a POVM effect 0 ≤ E ≤ 1 on the m q supplied copies ⊗_i (|ψ_i⟩⟨ψ_i|)^{⊗q} (NACTester); reason: for a fixed allocation the tester is a joint two-outcome POVM on the supplied state; ancillas, initial randomness and post-processing are absorbed into E, and a tester using fewer than q copies of a sample is an effect acting trivially on the unused copies
-- source:
--   Kawachi–Nakata–Takeuchi, Testing State and Unitary Designs, STOC 2027 submission (sha256 e2f0a429…), Theorem 2.2, p.4; formal versions Theorem 4.11 (p.37), Theorem 4.14 (p.41), Corollary 4.17 (p.44)

import Mathlib
import Definitions.Def_DesignTest_momentDist
import Definitions.Def_DesignTest_NACTester

set_option autoImplicit false

namespace DesignTest

open MeasureTheory

/-- **Theorem 2.2** (Sample and query complexity of SDT), in its formal form. A. Kawachi, Y. Nakata,
Y. Takeuchi, *Testing State and Unitary Designs*, STOC 2027 submission (sha256 e2f0a429…), Theorem 2.2,
p.4; formal versions Theorem 4.11 (p.37), Theorem 4.14 (p.41), Corollary 4.17 (p.44).

**(A) Upper bound (Theorem 4.11).** There is a universal `C > 0` such that for every `d ≥ 2`, `t ≥ 1`,
`ε_far ∈ (0, 1]`, `δ_fail ∈ (0, 1/2)` a non-adaptive coherent tester with
`m ≤ C √D_Sym/ε_far² · log(1/δ_fail)` samples, `q ≤ C t D_Sym^{3/2}/ε_far²` queries per sample and
`mq ≤ C t D_Sym²/ε_far⁴ · log(1/δ_fail)` accepts every exact state `t`-design with probability
`≥ 1 − δ_fail` and every `ε_far`-far input with probability `≤ δ_fail`.

**(B) General lower bound (Theorem 4.14).** For `d ≥ 2`, `t ≥ 1`, `ε_apx ∈ [0, ε_far)`,
`ε_far ∈ (0, 1/2)`, `δ_fail ∈ [0, 1/2)`, every measurable sample-based test `f : (pure states)^m → [0, 1]`
solving `(t, ε_apx, ε_far, δ_fail)`-SDT has `m ≥ √(2(1 − 2δ_fail)⌊D_Sym/2⌋)/(2ε_far)`.

**(C) Inverse-square bounds (Corollary 4.17).** For `ε_apx ∈ [0, ε_far)`, `ε_far ∈ (0, 1/4]`,
`δ_fail ∈ [0, 1/2)`: for `t = 1` and every `d ≥ 2`, `m ≥ (1 − 2δ_fail)√d/(128 ε_far²)`; for `t = 2` and
every prime-power `d ≥ 2`, `m ≥ (1 − 2δ_fail)√(d(d + 1)/2)/(256 ε_far²)`.

**Formalization Note.** Pure states are unit vectors of `ℂ^d` and inputs are probability measures on them;
`H` is the normalized sphere measure; `Dist₁^{(t)}(H, ν) = ½‖M_t(H) − M_t(ν)‖₁` with the trace norm as the
sum of singular values; `D_Sym = C(d + t − 1, t)`. The informal `O_t`/`Ω_t` bounds at a fixed `δ_fail`
follow from these explicit forms since `d^t/t! ≤ D_Sym ≤ (d + t − 1)^t/t!` (p.19). The lower-bound testers
are all measurable functions of the `m` sampled states (the classical-description model, which covers every
tester, p.21); the upper-bound tester is a POVM effect on the `mq` supplied copies. -/
theorem theorem_2_2 :
    -- (A) Theorem 4.11
    (∃ C : ℝ, 0 < C ∧ ∀ d t : ℕ, 2 ≤ d → 1 ≤ t → ∀ εfar δ : ℝ, 0 < εfar → εfar ≤ 1 → 0 < δ → δ < 1 / 2 →
      ∃ m q : ℕ,
        (m : ℝ) ≤ C * Real.sqrt (DSym d t : ℝ) / εfar ^ 2 * Real.log (1 / δ) ∧
        (q : ℝ) ≤ C * (t : ℝ) * (DSym d t : ℝ) ^ (3 / 2 : ℝ) / εfar ^ 2 ∧
        (m : ℝ) * (q : ℝ) ≤ C * (t : ℝ) * (DSym d t : ℝ) ^ 2 / εfar ^ 4 * Real.log (1 / δ) ∧
        ∃ T : NACTester d m q,
          (∀ (ν : Measure (PureVec d)) [IsProbabilityMeasure ν],
              momentDist t (haarState d) ν = 0 → 1 - δ ≤ T.acceptProb ν) ∧
          (∀ (ν : Measure (PureVec d)) [IsProbabilityMeasure ν],
              εfar < momentDist t (haarState d) ν → T.acceptProb ν ≤ δ)) ∧
    -- (B) Theorem 4.14
    (∀ d t : ℕ, 2 ≤ d → 1 ≤ t → ∀ εapx εfar δ : ℝ, 0 ≤ εapx → εapx < εfar → εfar < 1 / 2 → 0 ≤ δ →
      δ < 1 / 2 →
      ∀ (m : ℕ) (f : (Fin m → PureVec d) → ℝ), Measurable f → (∀ x, 0 ≤ f x ∧ f x ≤ 1) →
      (∀ (ν : Measure (PureVec d)) [IsProbabilityMeasure ν],
        momentDist t (haarState d) ν ≤ εapx → 1 - δ ≤ ∫ x, f x ∂(Measure.pi fun _ : Fin m => ν)) →
      (∀ (ν : Measure (PureVec d)) [IsProbabilityMeasure ν],
        εfar < momentDist t (haarState d) ν → ∫ x, f x ∂(Measure.pi fun _ : Fin m => ν) ≤ δ) →
      Real.sqrt (2 * (1 - 2 * δ) * ((DSym d t / 2 : ℕ) : ℝ)) / (2 * εfar) ≤ (m : ℝ)) ∧
    -- (C) Corollary 4.17, t = 1
    (∀ d : ℕ, 2 ≤ d → ∀ εapx εfar δ : ℝ, 0 ≤ εapx → εapx < εfar → εfar ≤ 1 / 4 → 0 ≤ δ → δ < 1 / 2 →
      ∀ (m : ℕ) (f : (Fin m → PureVec d) → ℝ), Measurable f → (∀ x, 0 ≤ f x ∧ f x ≤ 1) →
      (∀ (ν : Measure (PureVec d)) [IsProbabilityMeasure ν],
        momentDist 1 (haarState d) ν ≤ εapx → 1 - δ ≤ ∫ x, f x ∂(Measure.pi fun _ : Fin m => ν)) →
      (∀ (ν : Measure (PureVec d)) [IsProbabilityMeasure ν],
        εfar < momentDist 1 (haarState d) ν → ∫ x, f x ∂(Measure.pi fun _ : Fin m => ν) ≤ δ) →
      (1 - 2 * δ) * Real.sqrt (d : ℝ) / (128 * εfar ^ 2) ≤ (m : ℝ)) ∧
    -- (C) Corollary 4.17, t = 2
    (∀ d : ℕ, 2 ≤ d → IsPrimePow d → ∀ εapx εfar δ : ℝ, 0 ≤ εapx → εapx < εfar → εfar ≤ 1 / 4 →
      0 ≤ δ → δ < 1 / 2 →
      ∀ (m : ℕ) (f : (Fin m → PureVec d) → ℝ), Measurable f → (∀ x, 0 ≤ f x ∧ f x ≤ 1) →
      (∀ (ν : Measure (PureVec d)) [IsProbabilityMeasure ν],
        momentDist 2 (haarState d) ν ≤ εapx → 1 - δ ≤ ∫ x, f x ∂(Measure.pi fun _ : Fin m => ν)) →
      (∀ (ν : Measure (PureVec d)) [IsProbabilityMeasure ν],
        εfar < momentDist 2 (haarState d) ν → ∫ x, f x ∂(Measure.pi fun _ : Fin m => ν) ≤ δ) →
      (1 - 2 * δ) * Real.sqrt ((d : ℝ) * ((d : ℝ) + 1) / 2) / (256 * εfar ^ 2) ≤ (m : ℝ)) := by sorry

end DesignTest
