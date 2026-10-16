-- Prove2me | Theorems.Thm_CarlssonPartition_Approx_upper_bound
-- name    : CarlssonPartition.Approx.upper_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T08:04:34.098535+00:00
-- url     : https://prove2.me/theorems/660b755a-ceb9-4c4d-bbbb-55bff8366aeb
-- title:
--   Proof of Proposition 3, ec12 — corrected upper district bound
-- statement:
--   Suppose $R_1,\ldots,R_m$ is an $\varepsilon$ equitable partition for both $\mu_1$ and $\mu_2$, with $\lambda>0$, global workload below one, $\varepsilon\ge0$, and the corrected $\eta<1$. Let $L^*=L(m,\lambda,R,f)$ and $L_i=L(1,\lambda_i,R_i,f_i)$. For every district,
--   $$
--   L_i\le L^*\left(\frac{1+\eta}{1-\eta}\right)^2.
--   $$
--   This is the upper half of the paper's two sided comparison of district and benchmark leading times.
--
--   **Formalization Note** The printed $\eta$ uses a maximum; this statement uses the minimum required by the proof. The stable regime and $\eta<1$ make the denominator positive. $L_i$ is the district's Theorem 3 expression, not an independently formalized queueing expectation.
-- source:
--   Carlsson, Liu, Salari and Yu, Provably Good Region Partitioning for On-Time Last-Mile Delivery, accepted manuscript (SSRN 3915544; published in Operations Research 72(1):91–109, 2024, doi:10.1287/opre.2021.0588), proof of Proposition 3, p. ec12 (PDF 49), final display

import Mathlib
import Definitions.Def_CarlssonPartition_Approx_Setting

namespace CarlssonPartition.Approx

theorem upper_bound (I : Instance) (hI : I.Standing)
    (Rs : Fin I.m → Set CarlssonPartition.Equitable.Plane) (hP : I.IsPartition Rs)
    (lam ε : ℝ) (hlam : 0 < lam)
    (hstab : I.workload I.m lam I.R I.f < 1)
    (hε : 0 ≤ ε)
    (h1 : ∀ i, |I.mu1 (Rs i) - (1 / (I.m : ℝ)) * I.mu1 I.R| ≤ ε)
    (h2 : ∀ i, |I.mu2 (Rs i) - (1 / (I.m : ℝ)) * I.mu2 I.R| ≤ ε)
    (hη : I.eta lam ε < 1) :
    ∀ i, I.bvrLeading 1 (I.lamSub lam (Rs i)) (Rs i) (I.fSub (Rs i)) ≤
      I.bvrLeading I.m lam I.R I.f *
        ((1 + I.eta lam ε) / (1 - I.eta lam ε)) ^ 2 := by sorry
end CarlssonPartition.Approx
