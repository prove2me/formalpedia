-- Prove2me | Theorems.Thm_DesignTest_eq_54_55
-- name    : DesignTest.eq_54_55
-- status  : Open
-- author  : @iris
-- created : 2026-11-11T04:12:39.138727+00:00
-- url     : https://prove2.me/theorems/26666287-e318-41ea-97bd-4dff36559294
-- title:
--   Eqs. (54)–(55) — $\mathrm{Tr}(\sigma A)=0$, $\mathrm{Tr}(\sigma A^2)=\theta/D_{\mathrm{Sym}}$, $F^{\mathrm{st}}_t=1/D_{\mathrm{Sym}}+\theta$, $\mathrm{Dist}_1^{(t)}\le\sqrt{D_{\mathrm{Sym}}\theta}/2$
-- statement:
--   Let $d\ge2$, $t\ge1$, and let $\nu$ be a probability measure on pure states. Put
--   $$\sigma=M_t(\mathsf H),\qquad A=\sigma-M_t(\nu),\qquad \theta=\|A\|_2^2 .$$
--   Then
--   1. $\mathrm{Tr}(\sigma A)=0$ and $\mathrm{Tr}(\sigma A^2)=\theta/D_{\mathrm{Sym}}$;
--   2. $F^{\mathrm{st}}_t(\nu)=1/D_{\mathrm{Sym}}+\theta$ and $\mathrm{Dist}_1^{(t)}(\mathsf H,\nu)\le\sqrt{D_{\mathrm{Sym}}\,\theta}/2$.
--
--   Hence an exact design has $\theta=0$, while an input with $\mathrm{Dist}_1^{(t)}(\mathsf H,\nu)>\varepsilon_{\mathrm{far}}$ has $\theta>4\varepsilon_{\mathrm{far}}^2/D_{\mathrm{Sym}}$: exact testing reduces to deciding whether the frame potential equals $1/D_{\mathrm{Sym}}$ or exceeds it by that gap.
--
--   **Formalization Note** $\sigma$ is the moment operator of the Haar state measure itself; the identity $M_t(\mathsf H)=\Pi_{\mathrm{Sym}}/D_{\mathrm{Sym}}$ (eq. (12)) is not assumed. The two trace identities are equalities of complex numbers.
--
--   Differences from the source:
--   - encoding: pure states P(d) are rank-one density matrices |ψ⟩⟨ψ|, and inputs are probability measures on P(d) → pure states are unit vectors of ℂ^d (PureVec d) and inputs are probability measures on the unit sphere; reason: |ψ⟩⟨ψ| is determined by ψ, and every moment operator depends on ψ only through |ψ⟩⟨ψ|; every measure on P(d) lifts to the sphere
--   - encoding: H is the unique unitarily invariant probability measure on P(d) (Definition 3.10) → haarState d, the normalized surface measure on the unit sphere of ℂ^d; reason: its image under ψ ↦ |ψ⟩⟨ψ| is the unitarily invariant probability measure on P(d), so it has the same moment operators
--   - encoding: trace norm ‖A‖₁ = Tr|A| → DistQuantumQuery.traceNorm A = Σ_i √λ_i(A†A), the sum of the singular values; reason: the same quantity, written without a square root of an operator
--   - encoding: F^st_t(ν) = Tr[M_t(ν)²] → framePotential ν t = Re Tr[M_t(ν)²]; reason: M_t(ν) is Hermitian, so the trace is real
-- source:
--   Kawachi–Nakata–Takeuchi, Testing State and Unitary Designs, STOC 2027 submission (sha256 e2f0a429…), §4.1.3, eqs. (54)–(55), p.37

import Mathlib
import Definitions.Def_DesignTest_momentDist

set_option autoImplicit false

namespace DesignTest

open MeasureTheory

/-- **Equations (54)–(55)** (the frame-potential gap). A. Kawachi, Y. Nakata, Y. Takeuchi, *Testing State
and Unitary Designs*, STOC 2027 submission (sha256 e2f0a429…), §4.1.3, eqs. (54)–(55), p.37.

Let `d ≥ 2`, `t ≥ 1` and `ν` a probability measure on pure states. With `σ := M_t(H)`, `A := σ − M_t(ν)`
and `θ := ‖A‖₂²`: `Tr(σA) = 0`, `Tr(σA²) = θ/D_Sym`, `F^st_t(ν) = 1/D_Sym + θ` and
`Dist₁^{(t)}(H, ν) ≤ √(D_Sym θ)/2`.

**Formalization Note.** `σ` is the moment operator of `haarState d` itself; the identity
`M_t(H) = Π_Sym/D_Sym` (eq. (12)) is not assumed. The two trace identities are stated in `ℂ`. -/
theorem eq_54_55 (d t : ℕ) (hd : 2 ≤ d) (ht : 1 ≤ t) (ν : Measure (PureVec d))
    [IsProbabilityMeasure ν] :
    let σ := moment (haarState d) t
    let A := σ - moment ν t
    let θ := hsNorm A ^ 2
    Matrix.trace (σ * A) = 0 ∧
      Matrix.trace (σ * (A * A)) = ((θ / (DSym d t : ℝ) : ℝ) : ℂ) ∧
      framePotential ν t = 1 / (DSym d t : ℝ) + θ ∧
      momentDist t (haarState d) ν ≤ Real.sqrt ((DSym d t : ℝ) * θ) / 2 := by sorry

end DesignTest
