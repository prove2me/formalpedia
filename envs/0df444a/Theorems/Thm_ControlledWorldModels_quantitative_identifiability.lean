-- Prove2me | Theorems.Thm_ControlledWorldModels_quantitative_identifiability
-- name    : ControlledWorldModels.quantitative_identifiability
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-23T19:00:34.405091+00:00
-- url     : https://prove2.me/theorems/fcf7fc20-77e1-4b7d-8f1c-7a65ee596ea9
-- title:
--   Theorem 2: quantitative identifiability under the behavior policy
-- statement:
--   There are universal constants $c,C>0$ with the following property. Assume Assumptions 1–3, with $g$ invertible and bi-measurable, and $\gamma_{\rm rep}(\pi)>0$, $\rho_{\rm tr}(\pi)>0$. Let $h$ be a measurable encoder with $h(x_t)\sim\mathcal N(0,I_d)$, and let $F\in\mathcal F$ be a continuous predictor; $(h,F)$ need not minimize $\mathcal L_\pi$. Let $\Delta_{\rm enc}=\mathcal L_\pi(h,F_h^\star)-\mathcal L^\star$ and $\Delta_{\rm pred}=\mathbb E\|F(h(x_t),a_t)-F_h^\star(h(x_t),a_t)\|^2$. If $\Delta_{\rm enc}\le c\,\gamma_{\rm rep}(\pi)$, then there is $Q\in O(d)$ such that, with $\eta=\Delta_{\rm enc}/\gamma_{\rm rep}(\pi)$,
--
--   $$\mathbb E\|h(g(z_t))-Qz_t\|^2\le C\eta,$$
--
--   and, with $\varepsilon_F(z,a)=F(h(g(z)),a)-Q(Az+Ba)$,
--
--   $$\mathbb E_{P_\pi}\|\varepsilon_F(z_t,a_t)\|^2\le C\,\Delta_{\rm pred}+C\,(1+\|A\|_{\rm op}^2)\,\eta.$$
--
--   The representation error degrades as the inverse of the spectral margin, and predictor error enters the transition bound additively.
--
--   **Formalization Note** The constants are quantified before all data, including the dimensions. Errors are valued in $[0,\infty]$, so $\Delta_{\rm pred}=\infty$ is allowed and makes the second bound trivial.
-- source:
--   Zhang, Guan, Zhang, Li, Zhang and Li, On the Identifiability of Controlled World Models, arXiv:2607.22430v2 (2026), Section 3.3, Theorem 2, eq. (4), pp. 4-5; proof in Appendix B, p. 10

import Mathlib
import Definitions.Def_ControlledWorldModels_Basic

open MeasureTheory ProbabilityTheory

namespace ControlledWorldModels

theorem quantitative_identifiability.{u} :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
    ∀ {d m : ℕ} {X : Type u} [MeasurableSpace X] (g : (Fin d → ℝ) ≃ᵐ X)
      (A : Matrix (Fin d) (Fin d) ℝ) (B : Matrix (Fin d) (Fin m) ℝ)
      (μ : Measure ((Fin d → ℝ) × (Fin m → ℝ))) (ν : Measure (Fin d → ℝ)),
      IsJointGaussianPolicy μ → IsStationaryTransition A B μ ν →
      ∀ Fc : Set ((Fin d → ℝ) → (Fin m → ℝ) → Fin d → ℝ), IsRichPredictorClass A B μ ν Fc →
      0 < repMargin A B μ → 0 < transMargin μ →
      ∀ (h : X → Fin d → ℝ) (F : (Fin d → ℝ) → (Fin m → ℝ) → Fin d → ℝ),
      Measurable h → IsAdmissible (h ∘ g) → F ∈ Fc → Continuous (Function.uncurry F) →
      encExcess A B μ ν (h ∘ g) ≤ ENNReal.ofReal (c * repMargin A B μ) →
      ∃ Q : Matrix.orthogonalGroup (Fin d) ℝ,
        ∫⁻ z, ENNReal.ofReal (sqNorm (h (g z) - (Q : Matrix (Fin d) (Fin d) ℝ).mulVec z))
            ∂(stdGauss d) ≤
          ENNReal.ofReal C * (encExcess A B μ ν (h ∘ g) / ENNReal.ofReal (repMargin A B μ)) ∧
        ∫⁻ w, ENNReal.ofReal (sqNorm (F (h (g w.1)) w.2 -
            (Q : Matrix (Fin d) (Fin d) ℝ).mulVec (A.mulVec w.1 + B.mulVec w.2))) ∂μ ≤
          ENNReal.ofReal C * predExcess A B μ ν (h ∘ g) F +
            ENNReal.ofReal (C * (1 + opNorm A ^ 2)) *
              (encExcess A B μ ν (h ∘ g) / ENNReal.ofReal (repMargin A B μ)) := by sorry

end ControlledWorldModels
