-- Prove2me | Theorems.Thm_CarlssonPartition_Approx_district_leading
-- name    : CarlssonPartition.Approx.district_leading
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-16T08:04:25.954597+00:00
-- url     : https://prove2.me/theorems/a1675c8a-26d4-44d4-adea-211e0e43e464
-- title:
--   Proof of Theorem 6, ec5–ec6 — district leading term in μ₁ and μ₂
-- statement:
--   Let $R_i$ be a district in a partition of the service region and suppose its demand share $p(R_i)=\int_{R_i}f$ is positive. At arrival rate $\lambda$, its conditional demand density is $f_i=f/p(R_i)$ and its arrival rate is $\lambda_i=\lambda p(R_i)$. Theorem 3's single-vehicle leading term then has the form
--   $$
--   L(1,\lambda_i,R_i,f_i)=
--   \frac{\beta^2\lambda(1-1/q)^2\mu_1(R_i)^2}
--   {2v^2(1-\lambda\mu_2(R_i)/(vq))^2}.
--   $$
--   This normalization identity connects the district data to the two measures used in the approximate partition estimates.
--
--   **Formalization Note** The district term is constructed from its own $\lambda_i$ and $f_i$. Positive district demand is explicit because $f_i$ divides by that share. A partition is understood up to null sets.
-- source:
--   Carlsson, Liu, Salari and Yu, Provably Good Region Partitioning for On-Time Last-Mile Delivery, accepted manuscript (SSRN 3915544; published in Operations Research 72(1):91–109, 2024, doi:10.1287/opre.2021.0588), proof of Theorem 6, pp. ec5–ec6 (PDF 42–43), first equality on ec6

import Mathlib
import Definitions.Def_CarlssonPartition_Approx_Setting

namespace CarlssonPartition.Approx

theorem district_leading (I : Instance) (hI : I.Standing)
    (Rs : Fin I.m → Set CarlssonPartition.Equitable.Plane) (hP : I.IsPartition Rs)
    (i : Fin I.m) (hpr : 0 < I.pr (Rs i)) (lam : ℝ) :
    I.bvrLeading 1 (I.lamSub lam (Rs i)) (Rs i) (I.fSub (Rs i)) =
      I.beta ^ 2 * lam * (1 - 1 / (I.q : ℝ)) ^ 2 * I.mu1 (Rs i) ^ 2 /
        (2 * I.v ^ 2 * (1 - lam * I.mu2 (Rs i) / (I.v * (I.q : ℝ))) ^ 2) := by sorry
end CarlssonPartition.Approx
