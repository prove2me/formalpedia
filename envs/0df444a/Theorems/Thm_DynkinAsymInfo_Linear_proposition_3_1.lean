-- Prove2me | Theorems.Thm_DynkinAsymInfo_Linear_proposition_3_1
-- name    : DynkinAsymInfo.Linear.proposition_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T02:17:32.764981+00:00
-- url     : https://prove2.me/theorems/fc9b590a-79fa-433f-aa63-0dce6560167a
-- title:
--   Proposition 3.1 — ex-ante payoff through the posterior
-- statement:
--   Let $0\le f\le g$ be continuous, $\tau$ an admissible observation stopping time, and $(\Gamma^0,\Gamma^1)$ two admissible observation controls generating the informed stop. The ex-ante payoff is
--   $$J(\tau,\Gamma)=E\!\left[(1-\Pi_\tau)\left((1-\Gamma^0_\tau)f(X_\tau)+\int_0^\tau g(X_t)\,d\Gamma^0_t\right)+\Pi_\tau\left((1-\Gamma^1_\tau)f(X_\tau)+\int_0^\tau g(X_t)\,d\Gamma^1_t\right)\right].$$
--   The formula separates the two hidden types using Player 1's posterior. The Stieltjes integrals include a possible initial jump.
--
--   **Formalization Note.** This is the §6 GBM instance. The expectation is a nonnegative extended integral; the values of the total functions on the null event $\tau=\infty$ are immaterial.
-- source:
--   De Angelis, Ekström, Glover, Dynkin Games with Incomplete and Asymmetric Information, arXiv:1810.07674v5, pp. 7–8, Proposition 3.1, (11)

import Mathlib
import Definitions.Def_DynkinAsymInfo_Linear_Game

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace DynkinAsymInfo.Linear
set_option autoImplicit false

/-- De Angelis, Ekström, Glover, arXiv:1810.07674v5, pp. 7–8,
Proposition 3.1, (11), in the GBM instance. The type-conditioned controls
`G0,G1` generate the informed player's randomised stop. The Stieltjes
integrals include the jump at zero. -/
theorem proposition_3_1 {Ω : Type*} [MeasurableSpace Ω] (p : Params) (st : Setting Ω)
    (x pi : ℝ) (hx : 0 < x) (hpi : pi ∈ Set.Ioo 0 1)
    (f g : ℝ → ℝ)
    (hf : ContinuousOn f (Set.Ioi 0)) (hg : ContinuousOn g (Set.Ioi 0))
    (hfg : ∀ y, 0 < y → 0 ≤ f y ∧ f y ≤ g y)
    (tau : Ω → WithTop ℝ≥0) (htau : InT p st x pi tau)
    (G0 G1 : ℝ≥0 → Ω → ℝ)
    (hG0 : InA st (FX p st x pi) G0) (hG1 : InA st (FX p st x pi) G1) :
    J p st x pi f g tau (mixControl st pi G0 G1) =
      ∫⁻ a, (if tau a = ⊤ then 0 else
          ENNReal.ofReal (1 - Pi p st x pi (tau a).untopA a) *
            ENNReal.ofReal ((1 - G0 (tau a).untopA a) *
              f (X p st x pi (tau a).untopA a))) +
        ENNReal.ofReal (1 - Pi p st x pi (tau a).untopA a) *
          stInt (fun t => g (X p st x pi t a)) (fun t => G0 t a) (tau a) +
        (if tau a = ⊤ then 0 else
          ENNReal.ofReal (Pi p st x pi (tau a).untopA a) *
            ENNReal.ofReal ((1 - G1 (tau a).untopA a) *
              f (X p st x pi (tau a).untopA a))) +
        ENNReal.ofReal (Pi p st x pi (tau a).untopA a) *
          stInt (fun t => g (X p st x pi t a)) (fun t => G1 t a) (tau a) ∂st.P := by sorry

end DynkinAsymInfo.Linear
