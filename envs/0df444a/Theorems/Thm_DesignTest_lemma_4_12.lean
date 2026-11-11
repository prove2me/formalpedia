-- Prove2me | Theorems.Thm_DesignTest_lemma_4_12
-- name    : DesignTest.lemma_4_12
-- status  : Open
-- author  : @iris
-- created : 2026-11-11T04:12:41.217499+00:00
-- url     : https://prove2.me/theorems/12f5f7fe-bc2d-4943-8b76-13b44b19ce3f
-- title:
--   Lemma 4.12 — $\mathbb E[\widehat F]=1/D_{\mathrm{Sym}}+\theta$ and $\mathbb V(\widehat F)\le\frac4{m^2}(\frac1{D_{\mathrm{Sym}}}+\theta)+\frac4m(\frac\theta{D_{\mathrm{Sym}}}+\theta^{3/2})$
-- statement:
--   Let $d\ge2$, $t\ge1$, $m\ge2$, and let $\psi_1,\dots,\psi_m$ be independent samples from a probability measure $\nu$ on pure states. With $h_{ij}=|\langle\psi_i|\psi_j\rangle|^{2t}$, the empirical frame potential $\widehat F=\binom m2^{-1}\sum_{i<j}h_{ij}$ and $\theta=\|M_t(\mathsf H)-M_t(\nu)\|_2^2$,
--   $$\mathbb E[\widehat F]=\frac1{D_{\mathrm{Sym}}}+\theta,\qquad
--   \mathbb V(\widehat F)\le\frac4{m^2}\Big(\frac1{D_{\mathrm{Sym}}}+\theta\Big)+\frac4m\Big(\frac\theta{D_{\mathrm{Sym}}}+\theta^{3/2}\Big).$$
--
--   The bound shows that $O(\sqrt{D_{\mathrm{Sym}}}/\varepsilon_{\mathrm{far}}^2)$ samples make the fluctuation of $\widehat F$ small against the gap $4\varepsilon_{\mathrm{far}}^2/D_{\mathrm{Sym}}$; in the YES case ($\theta=0$) the covariance terms vanish.
--
--   **Formalization Note** Expectation and variance are taken under the product measure $\nu^{\otimes m}$, the variance as $\mathbb E[(\widehat F-\mathbb E\widehat F)^2]$; $\widehat F$ is continuous and bounded by $1$. $d\ge2$, $t\ge1$ are the standing assumptions of §4 (p.23).
--
--   Differences from the source:
--   - encoding: pure states P(d) are rank-one density matrices |ψ⟩⟨ψ|, and inputs are probability measures on P(d) → pure states are unit vectors of ℂ^d (PureVec d) and inputs are probability measures on the unit sphere; reason: |ψ⟩⟨ψ| is determined by ψ, and every moment operator depends on ψ only through |ψ⟩⟨ψ|; every measure on P(d) lifts to the sphere
--   - encoding: H is the unique unitarily invariant probability measure on P(d) (Definition 3.10) → haarState d, the normalized surface measure on the unit sphere of ℂ^d; reason: its image under ψ ↦ |ψ⟩⟨ψ| is the unitarily invariant probability measure on P(d), so it has the same moment operators
-- source:
--   Kawachi–Nakata–Takeuchi, Testing State and Unitary Designs, STOC 2027 submission (sha256 e2f0a429…), Lemma 4.12, eq. (59), p.37

import Mathlib
import Definitions.Def_DesignTest_momentDist
import Definitions.Def_DesignTest_empFrame

set_option autoImplicit false

namespace DesignTest

open MeasureTheory

/-- **Lemma 4.12** (Variance of the empirical frame potential). A. Kawachi, Y. Nakata, Y. Takeuchi,
*Testing State and Unitary Designs*, STOC 2027 submission (sha256 e2f0a429…), Lemma 4.12, eq. (59), p.37.

Let `d ≥ 2`, `t ≥ 1`, `m ≥ 2`, and let `ψ_1, …, ψ_m` be independent samples from a probability measure
`ν`. With `h_ij := |⟨ψ_i|ψ_j⟩|^{2t}`, `F̂ := C(m,2)⁻¹ Σ_{i<j} h_ij` and `θ := ‖M_t(H) − M_t(ν)‖₂²`:
`E[F̂] = 1/D_Sym + θ` and `V(F̂) ≤ (4/m²)(1/D_Sym + θ) + (4/m)(θ/D_Sym + θ^{3/2})`.

**Formalization Note.** Expectation and variance are under the product measure `ν^{⊗m}`; the variance is
written as `E[(F̂ − E F̂)²]` (`F̂` is continuous and bounded by `1`). `d ≥ 2`, `t ≥ 1` are the standing
assumptions of §4 (p.23). -/
theorem lemma_4_12 (d t m : ℕ) (hd : 2 ≤ d) (ht : 1 ≤ t) (hm : 2 ≤ m) (ν : Measure (PureVec d))
    [IsProbabilityMeasure ν] :
    let θ := hsNorm (moment (haarState d) t - moment ν t) ^ 2
    let P := Measure.pi fun _ : Fin m => ν
    ∫ ψ, empFrame t ψ ∂P = 1 / (DSym d t : ℝ) + θ ∧
      ∫ ψ, (empFrame t ψ - ∫ φ, empFrame t φ ∂P) ^ 2 ∂P ≤
        4 / (m : ℝ) ^ 2 * (1 / (DSym d t : ℝ) + θ) +
          4 / (m : ℝ) * (θ / (DSym d t : ℝ) + θ ^ (3 / 2 : ℝ)) := by sorry

end DesignTest
