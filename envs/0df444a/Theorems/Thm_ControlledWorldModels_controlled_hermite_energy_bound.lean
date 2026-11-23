-- Prove2me | Theorems.Thm_ControlledWorldModels_controlled_hermite_energy_bound
-- name    : ControlledWorldModels.controlled_hermite_energy_bound
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-23T18:57:38.915841+00:00
-- url     : https://prove2.me/theorems/db7bf76b-a488-49ae-9171-7ecea0b55cfa
-- title:
--   Lemma 2: controlled Hermite energy bound
-- statement:
--   Assume Assumptions 1–2. Let $R_\pi=\operatorname{Cov}(Az_t+Ba_t)$ have extreme eigenvalues $\lambda_1=\lambda_{\max}(R_\pi)<1$ and $\lambda_d=\lambda_{\min}(R_\pi)>0$. Let $h$ be an admissible encoder. Write the linear Hermite component of $z\mapsto h(g(z))$ under $z\sim\mathcal N(0,I_d)$ as $Lz$, with $L_{ij}=\mathbb E[h_i(g(z))z_j]$, and let $\tau_1=\operatorname{tr}(LL^\top)$. Then
--
--   $$J(h)\le\operatorname{tr}(R_\pi)-(\lambda_d-\lambda_1^2)(d-\tau_1).$$
--
--   This bound is the core of the identification argument: when $\lambda_d>\lambda_1^2$, every unit of energy outside the linear Hermite component costs predictable energy.
--
--   **Formalization Note** The paper's hypothesis $1>\lambda_1\ge\cdots\ge\lambda_d>0$ is stated through the largest and smallest eigenvalues only. $J(h)$, which is at most $d$ by Lemma 1, is converted to a real number.
-- source:
--   Zhang, Guan, Zhang, Li, Zhang and Li, On the Identifiability of Controlled World Models, arXiv:2607.22430v2 (2026), Appendix A, Lemma 2, p. 9

import Mathlib
import Definitions.Def_ControlledWorldModels_Basic

open MeasureTheory ProbabilityTheory

namespace ControlledWorldModels

theorem controlled_hermite_energy_bound {d m : ℕ} (A : Matrix (Fin d) (Fin d) ℝ) (B : Matrix (Fin d) (Fin m) ℝ)
    (μ : Measure ((Fin d → ℝ) × (Fin m → ℝ))) (ν : Measure (Fin d → ℝ))
    (hpol : IsJointGaussianPolicy μ) (htr : IsStationaryTransition A B μ ν)
    (e : (Fin d → ℝ) → Fin d → ℝ) (he : IsAdmissible e)
    (hmax : lamMax (repCov A B μ) < 1) (hmin : 0 < lamMin (repCov A B μ)) :
    (predEnergy A B μ ν e).toReal ≤ (repCov A B μ).trace -
      (lamMin (repCov A B μ) - lamMax (repCov A B μ) ^ 2) * ((d : ℝ) - hermEnergy1 e) := by sorry

end ControlledWorldModels
