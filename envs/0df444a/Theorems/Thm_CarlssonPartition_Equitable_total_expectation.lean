-- Prove2me | Theorems.Thm_CarlssonPartition_Equitable_total_expectation
-- name    : CarlssonPartition.Equitable.total_expectation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T06:17:09.607193+00:00
-- url     : https://prove2.me/theorems/0b5b9d0e-0a11-4a86-92e2-edfbed687858
-- title:
--   Proof of Theorem 5, p. ec5 — T = Σ_i P(x ∈ R_i)T_i, so T/T(π*) → 1 whenever every T_i/T(π*) → 1
-- statement:
--   Let the instance satisfy the standing assumptions and let $\{\mathscr R_1,\dots,\mathscr R_m\}$ be a partition of $\mathscr R$. Let $T(\pi^*)$ and $T_1,\dots,T_m$ be real functions of the arrival rate $\lambda$ such that, for every $i$,
--   $$\frac{T_i(\lambda)}{T(\pi^*)(\lambda)}\to1\qquad\text{as }\rho+\frac{2\lambda\iint_{\mathscr R}\|x-x_0\|f(x)\,dx}{mvq}\to1^-.$$
--   Then the overall expected delivery time given by the law of total expectation, $T=\sum_{i=1}^m\mathbb P(x\in\mathscr R_i)\,T_i$ with $\mathbb P(x\in\mathscr R_i)=\iint_{\mathscr R_i}f(x)\,dx$, satisfies
--   $$\frac{\sum_{i=1}^m\mathbb P(x\in\mathscr R_i)\,T_i(\lambda)}{T(\pi^*)(\lambda)}\to1$$
--   along the same heavy-traffic limit.
--
--   This is the final step of the proofs of Theorems 5 and 6: once each district is asymptotically as fast as $\pi^*$, so is the region partitioning policy as a whole.
--
--   **Formalization Note.** The content is that the district probabilities sum to $\iint_{\mathscr R}f=1$ for a partition up to null sets, together with averaging of ratios under a probability vector.
-- source:
--   Carlsson, Liu, Salari and Yu, Provably Good Region Partitioning for On-Time Last-Mile Delivery, accepted manuscript (SSRN 3915544; published in Operations Research 72(1):91–109, 2024, doi:10.1287/opre.2021.0588), p. ec5, proof of Theorem 5, display after 'Therefore, the expected delivery time to the whole service region is'

import Mathlib
import Definitions.Def_CarlssonPartition_Equitable_Setting

open Filter Topology MeasureTheory

namespace CarlssonPartition.Equitable

theorem total_expectation (I : Instance) (hI : I.Standing)
    (Rs : Fin I.m → Set Plane) (hP : I.IsPartition Rs)
    (Tstar : ℝ → ℝ) (T : Fin I.m → ℝ → ℝ)
    (hT : ∀ i, Tendsto (fun lam => T i lam / Tstar lam) (I.heavy I.m I.R I.f) (𝓝 1)) :
    Tendsto (fun lam => (∑ i, I.pr (Rs i) * T i lam) / Tstar lam) (I.heavy I.m I.R I.f) (𝓝 1) := by sorry

end CarlssonPartition.Equitable
