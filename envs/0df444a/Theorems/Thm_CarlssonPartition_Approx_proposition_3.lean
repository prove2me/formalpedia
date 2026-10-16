-- Prove2me | Theorems.Thm_CarlssonPartition_Approx_proposition_3
-- name    : CarlssonPartition.Approx.proposition_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T08:04:38.944816+00:00
-- url     : https://prove2.me/theorems/c110c5e6-a64f-4759-8b4b-edf90e6bdca0
-- title:
--   Proposition 3, p. 21 — ε-equitable district error bound with corrected η
-- statement:
--   Consider a compact convex service region with normalized Lipschitz demand density, $m$ identical vehicles, a depot, capacity $q$, speed $v$, mean service time $\bar s$, and geometric constant $\beta$. Let $R_1,\ldots,R_m$ partition the region and let their $\mu_1$ and $\mu_2$ shares differ from one $m$th of the corresponding whole-region shares by at most $\varepsilon$. For $\lambda>0$ in the stable regime, $\varepsilon\ge0$, and corrected $\eta<1$, write $L_i$ for the single-vehicle Theorem 3 leading term using district $i$'s own arrival rate and conditional density and $L^*$ for the full-region term. Then
--   $$
--   \lvert L_i-L^*\rvert\le
--   \frac{4\eta}{(1-\eta)^2}L^*\qquad\text{for every }i.
--   $$
--   The bound quantifies the loss in each district from approximate equitability.
--
--   **Formalization Note** The source prints $\eta=\varepsilon/\max\{\mu_1(R)/m,(vq/\lambda)(1-\lambda\mu_2(R)/(mvq))\}$, which makes the proposition false; the formal statement uses $\min$ as the proof requires. Its “for small $\varepsilon$” is expressed as $\eta<1$. $L_i$ and $L^*$ are Theorem 3 leading expressions at fixed $\lambda$, rather than the underlying stochastic delivery-time functions.
-- source:
--   Carlsson, Liu, Salari and Yu, Provably Good Region Partitioning for On-Time Last-Mile Delivery, accepted manuscript (SSRN 3915544; published in Operations Research 72(1):91–109, 2024, doi:10.1287/opre.2021.0588), p. 21, Proposition 3 (PDF 22); proof pp. ec12–ec13 (PDF 49–50)

import Mathlib
import Definitions.Def_CarlssonPartition_Approx_Setting

namespace CarlssonPartition.Approx

theorem proposition_3 (I : Instance) (hI : I.Standing)
    (Rs : Fin I.m → Set CarlssonPartition.Equitable.Plane) (hP : I.IsPartition Rs)
    (lam ε : ℝ) (hlam : 0 < lam)
    (hstab : I.workload I.m lam I.R I.f < 1)
    (hε : 0 ≤ ε)
    (h1 : ∀ i, |I.mu1 (Rs i) - (1 / (I.m : ℝ)) * I.mu1 I.R| ≤ ε)
    (h2 : ∀ i, |I.mu2 (Rs i) - (1 / (I.m : ℝ)) * I.mu2 I.R| ≤ ε)
    (hη : I.eta lam ε < 1) :
    ∀ i, |I.bvrLeading 1 (I.lamSub lam (Rs i)) (Rs i) (I.fSub (Rs i)) -
      I.bvrLeading I.m lam I.R I.f| ≤
      4 * I.eta lam ε / (1 - I.eta lam ε) ^ 2 *
        I.bvrLeading I.m lam I.R I.f := by sorry
end CarlssonPartition.Approx
