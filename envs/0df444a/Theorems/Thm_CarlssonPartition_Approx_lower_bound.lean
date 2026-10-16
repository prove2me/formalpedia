-- Prove2me | Theorems.Thm_CarlssonPartition_Approx_lower_bound
-- name    : CarlssonPartition.Approx.lower_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T08:04:27.116671+00:00
-- url     : https://prove2.me/theorems/f457326a-2948-4f7f-a3a3-875d7d9d66ce
-- title:
--   Proof of Proposition 3, ec13 — corrected lower district bound
-- statement:
--   Under the same standing model, $\varepsilon$ equitability, positive stable arrival rate, nonnegative tolerance, and corrected $\eta<1$, write $L^*$ for the full-region Theorem 3 leading term and $L_i$ for the single-vehicle term formed from district $i$'s arrival rate and conditional density. Then every district obeys
--   $$
--   L^*\left(\frac{1-\eta}{1+\eta}\right)^2\le L_i.
--   $$
--   Together with the upper estimate, this controls both directions of a district's departure from the benchmark.
--
--   **Formalization Note** The printed $\eta$ uses a maximum; the minimum is used here. $\eta<1$ ensures positive factors in the comparison. The statement concerns leading expressions at fixed $\lambda$.
-- source:
--   Carlsson, Liu, Salari and Yu, Provably Good Region Partitioning for On-Time Last-Mile Delivery, accepted manuscript (SSRN 3915544; published in Operations Research 72(1):91–109, 2024, doi:10.1287/opre.2021.0588), proof of Proposition 3, p. ec13 (PDF 50), first display

import Mathlib
import Definitions.Def_CarlssonPartition_Approx_Setting

namespace CarlssonPartition.Approx

theorem lower_bound (I : Instance) (hI : I.Standing)
    (Rs : Fin I.m → Set CarlssonPartition.Equitable.Plane) (hP : I.IsPartition Rs)
    (lam ε : ℝ) (hlam : 0 < lam)
    (hstab : I.workload I.m lam I.R I.f < 1)
    (hε : 0 ≤ ε)
    (h1 : ∀ i, |I.mu1 (Rs i) - (1 / (I.m : ℝ)) * I.mu1 I.R| ≤ ε)
    (h2 : ∀ i, |I.mu2 (Rs i) - (1 / (I.m : ℝ)) * I.mu2 I.R| ≤ ε)
    (hη : I.eta lam ε < 1) :
    ∀ i, I.bvrLeading I.m lam I.R I.f *
      ((1 - I.eta lam ε) / (1 + I.eta lam ε)) ^ 2 ≤
        I.bvrLeading 1 (I.lamSub lam (Rs i)) (Rs i) (I.fSub (Rs i)) := by sorry
end CarlssonPartition.Approx
