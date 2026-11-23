-- Prove2me | Theorems.Thm_ControlledWorldModels_approx_predictable_energy_gap
-- name    : ControlledWorldModels.approx_predictable_energy_gap
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-23T18:59:22.454445+00:00
-- url     : https://prove2.me/theorems/a2b2964e-1407-4dad-9b3d-3da0aef95358
-- title:
--   Lemma 3 (as proved, with C = 1): approximate predictable-energy gap
-- statement:
--   Assume Assumptions 1–2 and $\gamma_{\rm rep}(\pi)=\lambda_{\min}(R_\pi)-\lambda_{\max}(R_\pi)^2>0$. Let $h$ be an admissible encoder. Write $h(g(z))=Lz+\tilde g(z)$, where $Lz$ is the linear Hermite component under $z\sim\mathcal N(0,I_d)$, and let $r=\mathbb E\|\tilde g(z)\|^2$. If $\Delta\ge0$ and $\mathcal L_\pi(h,F_h^\star)\le\mathcal L^\star+\Delta$ with $\mathcal L^\star=d-\operatorname{tr}R_\pi$, then
--
--   $$r\le\frac{\Delta}{\gamma_{\rm rep}(\pi)}.$$
--
--   A small encoder excess risk thus forces small energy outside the linear Hermite component.
--
--   **Formalization Note** The paper states $r\le C\Delta_{\rm enc}/\gamma_{\rm rep}(\pi)$ with an unspecified constant $C$. Its proof ends with $(\lambda_d-\lambda_1^2)\,r\le\Delta_{\rm enc}$, i.e. $C=1$, which is the statement formalized. The paper's symbol $g$ for the nonlinear part is written $\tilde g$ here to avoid a clash with the observation map.
-- source:
--   Zhang, Guan, Zhang, Li, Zhang and Li, On the Identifiability of Controlled World Models, arXiv:2607.22430v2 (2026), Appendix B, Lemma 3, pp. 9-10 (setting: Section 3.3, Theorem 2, p. 4)

import Mathlib
import Definitions.Def_ControlledWorldModels_Basic

open MeasureTheory ProbabilityTheory

namespace ControlledWorldModels

theorem approx_predictable_energy_gap {d m : ℕ} (A : Matrix (Fin d) (Fin d) ℝ) (B : Matrix (Fin d) (Fin m) ℝ)
    (μ : Measure ((Fin d → ℝ) × (Fin m → ℝ))) (ν : Measure (Fin d → ℝ))
    (hpol : IsJointGaussianPolicy μ) (htr : IsStationaryTransition A B μ ν)
    (e : (Fin d → ℝ) → Fin d → ℝ) (he : IsAdmissible e) (hrep : 0 < repMargin A B μ)
    (Δ : ℝ) (hΔ0 : 0 ≤ Δ)
    (hΔ : condLoss A B μ ν e ≤ ENNReal.ofReal (optValue A B μ) + ENNReal.ofReal Δ) :
    nonlinEnergy e ≤ ENNReal.ofReal (Δ / repMargin A B μ) := by sorry

end ControlledWorldModels
