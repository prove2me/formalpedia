-- Prove2me | Theorems.Thm_DynkinAsymInfo_Linear_filter_likelihood
-- name    : DynkinAsymInfo.Linear.filter_likelihood
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T02:17:30.124822+00:00
-- url     : https://prove2.me/theorems/6178fb13-3640-41e1-89d3-69cba899d84f
-- title:
--   §3 (8), (20)–(23) — posterior and corrected likelihood identity
-- statement:
--   For $x>0$, prior $\pi\in(0,1)$, and each $t\ge0$, write $\phi=\pi/(1-\pi)$. On every event $A\in\mathcal F^X_t$,
--   $$P^1(A)=\int_A\frac{\Phi_t}{\phi}\,dP^0,\qquad P(A\cap\{\theta=1\})=\int_A\Pi_t\,dP.$$
--   Thus $\Pi_t$ is a version of the observed posterior and $\Phi_t/\phi$ is the type-one versus type-zero likelihood ratio.
--
--   **Formalization Note.** The paper's (23) prints $\Phi_t=dP^1/dP^0$. Equations (19)–(21) show the missing factor $1/\phi$; at $t=0$ a derivative equals one while $\Phi_0=\phi$. The corrected identity is used here.
-- source:
--   De Angelis, Ekström, Glover, Dynkin Games with Incomplete and Asymmetric Information, arXiv:1810.07674v5, pp. 7, 9, (8) and (20)–(23)

import Mathlib
import Definitions.Def_DynkinAsymInfo_Linear_Game

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace DynkinAsymInfo.Linear
set_option autoImplicit false

/-- De Angelis, Ekström, Glover, arXiv:1810.07674v5, pp. 7, 9,
(8), (20)–(23). The observation likelihood and posterior identities.

**Formalization Note.** Equation (23) omits the initial odds: since `Φ₀=ϕ`, the
Radon–Nikodym derivative of `P¹` with respect to `P⁰` is `Φ/ϕ`, as follows
directly from (20)–(21). The printed `Φ` alone cannot be that derivative
at time zero unless `ϕ=1`. The second identity is the posterior (8). -/
theorem filter_likelihood {Ω : Type*} [MeasurableSpace Ω]
    (p : Params) (st : Setting Ω) (x pi : ℝ)
    (hx : 0 < x) (hpi : pi ∈ Set.Ioo 0 1) (t : ℝ≥0) :
    let phi := pi / (1 - pi)
    (∀ A, MeasurableSet[FX p st x pi t] A →
      Ptype st pi 1 A =
        ∫⁻ a in A, ENNReal.ofReal (Phi p st x pi t a / phi) ∂(Ptype st pi 0)) ∧
    (∀ A, MeasurableSet[FX p st x pi t] A →
      st.P (A ∩ {a | hiddenType st pi a = 1}) =
        ∫⁻ a in A, ENNReal.ofReal (Pi p st x pi t a) ∂st.P) := by sorry

end DynkinAsymInfo.Linear
