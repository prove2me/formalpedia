-- Prove2me | Theorems.Thm_BrownianEnergyRep_corollary_5_6
-- name    : BrownianEnergyRep.corollary_5_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T07:02:09.76269+00:00
-- url     : https://prove2.me/theorems/8e2587ce-8962-4977-be20-105c5ef0424a
-- title:
--   Corollary 5.6 — $\mathcal Fe^{\langle h,\cdot\rangle/2-|h|^2/4}=e^{\frac i2\langle h,\cdot\rangle}$ (corrected: normalization and sign)
-- statement:
--   Let $(H,W,\Gamma)$ be an abstract Wiener space with Fourier-Wiener transform $\mathcal F$. For any $h\in H$,
--   $$
--   \mathcal Fe^{\frac12\langle h,\cdot\rangle-\frac14|h|^2}=e^{\frac i2\langle h,\cdot\rangle} .
--   $$
--   It is Proposition 5.5 at $R=I$ and $f\equiv1$.
--
--   Differences from the source:
--   - encoding: F by Definition 17 of Driver-Hall, with a heuristic integral formula → the unitary with Fϕ̂ = e^{−|ϕ|²}e^{−⟨ϕ,·⟩}, the second identity of (5.2); reason: both families are total with Gram matrix exp(−½|ϕ−ψ|²), so this determines F
--   - encoding: ⟨h,w⟩ for h ∈ H → the L²(Γ) limit, as a representative chosen by Classical.epsilon (pairing); reason: unique a.e. by pairing_isometry
--   - correction: F e^{⟨h,w⟩−|h|²/2} = e^{−i⟨h,w⟩/2} → F e^{⟨h,w⟩/2−|h|²/4} = e^{(i/2)⟨h,w⟩}; reason: the printed left side has L² norm e^{|h|²/2} and the right side has norm 1, while F is unitary
-- source:
--   Albeverio, Driver, Gordina, Vershik, Equivalence of the Brownian and energy representations, arXiv:1511.07378v1, Corollary 5.6, p.18 (corrected)

import Mathlib
import Definitions.Def_BrownianEnergyRep_AbstractWienerSpace
import Definitions.Def_BrownianEnergyRep_AbstractWienerSpace_pairing
import Definitions.Def_BrownianEnergyRep_IsFourierWiener

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology ContDiff RealInnerProductSpace

namespace BrownianEnergyRep

/-- Corollary 5.6 (arXiv:1511.07378v1, p.18), corrected: `F e^{⟨h,·⟩/2 − |h|²/4} = e^{(i/2)⟨h,·⟩}` for `h ∈ H`. -/
theorem corollary_5_6 {H W : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] [NormedAddCommGroup W] [NormedSpace ℝ W] [MeasurableSpace W]
    (A : AbstractWienerSpace H W) (F : Lp ℂ 2 A.Γ ≃ₗᵢ[ℂ] Lp ℂ 2 A.Γ)
    (hF : IsFourierWiener A F) (h : H) :
    ∃ hm : MemLp (fun w => (Real.exp (A.pairing h w / 2 - ‖h‖ ^ 2 / 4) : ℂ)) 2 A.Γ,
      (F (hm.toLp _) : W → ℂ) =ᵐ[A.Γ]
        fun w => Complex.exp (Complex.I / 2 * (A.pairing h w : ℂ)) := by sorry

end BrownianEnergyRep
