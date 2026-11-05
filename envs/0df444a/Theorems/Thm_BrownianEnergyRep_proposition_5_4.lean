-- Prove2me | Theorems.Thm_BrownianEnergyRep_proposition_5_4
-- name    : BrownianEnergyRep.proposition_5_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T07:02:36.631365+00:00
-- url     : https://prove2.me/theorems/574f90f5-db3c-4430-8e21-af6241288d8d
-- title:
--   Proposition 5.4 — density of exponentials and the Fourier-Wiener transform
-- statement:
--   Let $(H,W,\Gamma)$ be an abstract Wiener space.
--
--   1. $\mathcal E=\mathrm{Span}_{\mathbb C}\{\widehat\varphi(w)=e^{i\langle\varphi,w\rangle},\ \varphi\in W^*\}$ is an algebra which is dense in $L^2(W,\Gamma)$.
--   2. For any $\varphi\in W^*$,
--   $$
--   \int_W\widehat\varphi(w)\,d\Gamma(w)=e^{-\frac{|\varphi|^2_{H^*}}2},\quad(\mathcal F\widehat\varphi)(w)=e^{-|\varphi|^2_{H^*}}e^{-\langle\varphi,w\rangle},\quad\big(\mathcal Fe^{\langle\varphi,\cdot\rangle}\big)(w)=e^{|\varphi|^2_{H^*}}\widehat\varphi(w).
--   $$
--
--   Moreover the unitary $\mathcal F$ with the second identity exists and is unique, and $\mathcal F^4=I$. These are the identities that reduce Proposition 5.5 to computations on exponentials.
--
--   Differences from the source:
--   - encoding: F by Definition 17 of Driver-Hall, with a heuristic integral formula → the unitary with Fϕ̂ = e^{−|ϕ|²}e^{−⟨ϕ,·⟩}, the second identity of (5.2); reason: both families are total with Gram matrix exp(−½|ϕ−ψ|²), so this determines F
-- source:
--   Albeverio, Driver, Gordina, Vershik, Equivalence of the Brownian and energy representations, arXiv:1511.07378v1, Proposition 5.4, p.17; p.17 for $\mathcal F^4=I$

import Mathlib
import Definitions.Def_BrownianEnergyRep_AbstractWienerSpace
import Definitions.Def_BrownianEnergyRep_IsFourierWiener

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology ContDiff RealInnerProductSpace

namespace BrownianEnergyRep

/-- Proposition 5.4 (arXiv:1511.07378v1, p.17) with the existence, uniqueness and `F⁴ = I` of the Fourier-Wiener transform. -/
theorem proposition_5_4 {H W : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [MeasurableSpace W]
    (A : AbstractWienerSpace H W) :
    (∃ B : Subalgebra ℂ (W → ℂ),
      Subalgebra.toSubmodule B = Submodule.span ℂ (Set.range (hat (W := W)))) ∧
    Dense {f : Lp ℂ 2 A.Γ | ∃ e ∈ Submodule.span ℂ (Set.range (hat (W := W))),
      (f : W → ℂ) =ᵐ[A.Γ] e} ∧
    (∀ φ : StrongDual ℝ W, ∫ w, hat φ w ∂A.Γ = Real.exp (-‖φ.comp A.j‖ ^ 2 / 2)) ∧
    (∃! F, IsFourierWiener A F) ∧
    ∀ F, IsFourierWiener A F →
      (∀ (φ : StrongDual ℝ W) (hφ : MemLp (fun w => (Real.exp (φ w) : ℂ)) 2 A.Γ),
        (F (hφ.toLp _) : W → ℂ) =ᵐ[A.Γ]
          fun w => (Real.exp (‖φ.comp A.j‖ ^ 2) : ℂ) * hat φ w) ∧
      ∀ f, F (F (F (F f))) = f := by sorry

end BrownianEnergyRep
