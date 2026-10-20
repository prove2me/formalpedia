-- Prove2me | Theorems.Thm_DynkinAsymInfo_Linear_corollary_3_3
-- name    : DynkinAsymInfo.Linear.corollary_3_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T02:17:28.494828+00:00
-- url     : https://prove2.me/theorems/6dad33fd-6022-4547-a9f1-32e890e5e816
-- title:
--   Corollary 3.3 — payoff under the type-zero law
-- statement:
--   For the admissible game and $\phi=\pi/(1-\pi)$, the ex-ante payoff can be evaluated entirely under the type-zero conditional law:
--   $$J(\tau,\Gamma)=\frac{1}{1+\phi}E^0\!\left[(1-\Gamma^0_\tau)f(X_\tau)+\int_0^\tau g(X_t)d\Gamma^0_t+(1-\Gamma^1_\tau)\Phi_\tau f(X_\tau)+\int_0^\tau\Phi_tg(X_t)d\Gamma^1_t\right].$$
--   The identity is the likelihood-weighted version of Proposition 3.1. $\Phi_t$ is posterior odds, and its factor in this formula is consistent with the corrected likelihood derivative $\Phi_t/\phi$.
--
--   **Formalization Note.** This is the §6 GBM instance, with conditional expectation under $P^0$ and nonnegative extended integrals.
-- source:
--   De Angelis, Ekström, Glover, Dynkin Games with Incomplete and Asymmetric Information, arXiv:1810.07674v5, p. 9, Corollary 3.3, (24)

import Mathlib
import Definitions.Def_DynkinAsymInfo_Linear_Game

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace DynkinAsymInfo.Linear
set_option autoImplicit false

/-- De Angelis, Ekström, Glover, arXiv:1810.07674v5, p. 9,
Corollary 3.3, (24), in the GBM instance. The second expectation under `P⁰`
is weighted by the likelihood odds `Φ`. The outer factor is `(1+ϕ)⁻¹`. -/
theorem corollary_3_3 {Ω : Type*} [MeasurableSpace Ω] (p : Params) (st : Setting Ω)
    (x pi : ℝ) (hx : 0 < x) (hpi : pi ∈ Set.Ioo 0 1)
    (f g : ℝ → ℝ)
    (hf : ContinuousOn f (Set.Ioi 0)) (hg : ContinuousOn g (Set.Ioi 0))
    (hfg : ∀ y, 0 < y → 0 ≤ f y ∧ f y ≤ g y)
    (tau : Ω → WithTop ℝ≥0) (htau : InT p st x pi tau)
    (G0 G1 : ℝ≥0 → Ω → ℝ)
    (hG0 : InA st (FX p st x pi) G0) (hG1 : InA st (FX p st x pi) G1) :
    let phi := pi / (1 - pi)
    J p st x pi f g tau (mixControl st pi G0 G1) =
      ENNReal.ofReal (1 / (1 + phi)) *
        (J0 p st x pi f g tau G0 +
          ∫⁻ a, (if tau a = ⊤ then 0 else
              ENNReal.ofReal ((1 - G1 (tau a).untopA a) *
                Phi p st x pi (tau a).untopA a *
                f (X p st x pi (tau a).untopA a))) +
            stInt (fun t => Phi p st x pi t a * g (X p st x pi t a))
              (fun t => G1 t a) (tau a) ∂(Ptype st pi 0)) := by sorry

end DynkinAsymInfo.Linear
