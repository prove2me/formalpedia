-- Prove2me | Theorems.Thm_DesignTest_eq_64_66
-- name    : DesignTest.eq_64_66
-- status  : Open
-- author  : @iris
-- created : 2026-11-11T04:14:15.918202+00:00
-- url     : https://prove2.me/theorems/fd9ee87a-8816-4ee9-b24c-8eb9b37314cf
-- title:
--   Eqs. (64), (66) — one batch errs with probability $<1/8$ on every exact design and every $\varepsilon_{\mathrm{far}}$-far input
-- statement:
--   Let $d\ge2$, $t\ge1$, $\varepsilon_{\mathrm{far}}\in(0,1]$, and run one batch of the frame-potential tester: $m_0=\lceil C\sqrt{D_{\mathrm{Sym}}}/\varepsilon_{\mathrm{far}}^2\rceil$ samples with $C=256$, $D_{\mathrm{Sym}}$ SWAP tests per unordered pair, and acceptance iff $\widetilde F\le 1/D_{\mathrm{Sym}}+2\varepsilon_{\mathrm{far}}^2/D_{\mathrm{Sym}}$. For every probability measure $\nu$ on pure states:
--   1. if $\nu$ is an exact state $t$-design, then
--   $$\Pr[\text{reject}]\le\frac1{64}+\frac{16}{9C^2}<\frac18;\qquad(64)$$
--   2. if $\mathrm{Dist}_1^{(t)}(\mathsf H,\nu)>\varepsilon_{\mathrm{far}}$, then
--   $$\Pr[\text{accept}]\le\frac1{64}+\frac{16}{9}\Big(\frac5{C^2}+\frac{11}C\Big)<\frac18.\qquad(66)$$
--
--   Both bounds are uniform over the inputs; majority amplification of independent batches then gives any failure probability $\delta_{\mathrm{fail}}$.
--
--   **Formalization Note** The batch acceptance probability is the integral over $\nu^{\otimes m_0}$ of the conditional acceptance probability, where conditional on the samples the SWAP outcomes are independent $\pm1$ variables with means $h_{ij}$ (`batchAcceptProb`). The rejection probability is one minus the acceptance probability.
--
--   Differences from the source:
--   - encoding: pure states P(d) are rank-one density matrices |ψ⟩⟨ψ|, and inputs are probability measures on P(d) → pure states are unit vectors of ℂ^d (PureVec d) and inputs are probability measures on the unit sphere; reason: |ψ⟩⟨ψ| is determined by ψ, and every moment operator depends on ψ only through |ψ⟩⟨ψ|; every measure on P(d) lifts to the sphere
--   - encoding: H is the unique unitarily invariant probability measure on P(d) (Definition 3.10) → haarState d, the normalized surface measure on the unit sphere of ℂ^d; reason: its image under ψ ↦ |ψ⟩⟨ψ| is the unitarily invariant probability measure on P(d), so it has the same moment operators
--   - encoding: trace norm ‖A‖₁ = Tr|A| → DistQuantumQuery.traceNorm A = Σ_i √λ_i(A†A), the sum of the singular values; reason: the same quantity, written without a square root of an operator
--   - encoding: one batch of SWAP tests performed on the supplied copies → the batch's classical outcome law: conditionally on the samples, independent ±1 outcomes with Pr[+1] = (1 + h_ij)/2 (batchAcceptProb); reason: each SWAP test has this outcome law (swap_test_expectation) and the tests act on disjoint copies, so they are conditionally independent (p.38)
-- source:
--   Kawachi–Nakata–Takeuchi, Testing State and Unitary Designs, STOC 2027 submission (sha256 e2f0a429…), proof of Theorem 4.11, eqs. (64) and (66), p.39

import Mathlib
import Definitions.Def_DesignTest_momentDist
import Definitions.Def_DesignTest_batchAcceptProb

set_option autoImplicit false

namespace DesignTest

open MeasureTheory

/-- **Equations (64) and (66)** (one batch errs with probability below `1/8`). A. Kawachi, Y. Nakata,
Y. Takeuchi, *Testing State and Unitary Designs*, STOC 2027 submission (sha256 e2f0a429…), proof of
Theorem 4.11, eqs. (64) and (66), p.39.

Let `d ≥ 2`, `t ≥ 1`, `ε_far ∈ (0, 1]`. One batch of the frame-potential tester (`m₀ = ⌈256√D_Sym/ε_far²⌉`
samples, `D_Sym` SWAP tests per unordered pair, accept iff `F̃ ≤ 1/D_Sym + 2ε_far²/D_Sym`) satisfies, for
every probability measure `ν`:
1. if `ν` is an exact state `t`-design, `Pr[reject] ≤ 1/64 + 16/(9C²) < 1/8`, `C = 256` ((64));
2. if `Dist₁^{(t)}(H, ν) > ε_far`, `Pr[accept] ≤ 1/64 + (16/9)(5/C² + 11/C) < 1/8` ((66)).

**Formalization Note.** `batchAcceptProb t ε_far ν` is the batch's acceptance probability: the integral
over `ν^{⊗m₀}` of the conditional acceptance probability, the SWAP outcomes being conditionally independent
`±1` variables with means `h_ij` (see `swap_test_expectation`). -/
theorem eq_64_66 (d t : ℕ) (hd : 2 ≤ d) (ht : 1 ≤ t) (εfar : ℝ) (hε0 : 0 < εfar) (hε1 : εfar ≤ 1) :
    (∀ (ν : Measure (PureVec d)) [IsProbabilityMeasure ν], momentDist t (haarState d) ν = 0 →
        1 - batchAcceptProb t εfar ν ≤ 1 / 64 + 16 / (9 * (256 : ℝ) ^ 2) ∧
          1 / 64 + 16 / (9 * (256 : ℝ) ^ 2) < 1 / 8) ∧
      (∀ (ν : Measure (PureVec d)) [IsProbabilityMeasure ν], εfar < momentDist t (haarState d) ν →
        batchAcceptProb t εfar ν ≤ 1 / 64 + 16 / 9 * (5 / (256 : ℝ) ^ 2 + 11 / 256) ∧
          1 / 64 + 16 / 9 * (5 / (256 : ℝ) ^ 2 + 11 / 256) < 1 / 8) := by sorry

end DesignTest
