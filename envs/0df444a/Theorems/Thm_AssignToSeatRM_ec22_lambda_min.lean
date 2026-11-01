-- Prove2me | Theorems.Thm_AssignToSeatRM_ec22_lambda_min
-- name    : AssignToSeatRM.ec22_lambda_min
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:27:48.48899+00:00
-- url     : https://prove2.me/theorems/1516d6e9-db68-4427-88ef-a7651742afbb
-- title:
--   (EC.22) — remaining expected demand of every arriving itinerary is at least $\lambda_{\min}(\theta T_{ij}-t)$
-- statement:
--   Let $\lambda^t_{ij}$ be arrival probabilities ($\lambda^t_{ij}\ge0$, $\sum_{i\le j}\lambda^t_{ij}\le1$, $t\in[T]$). For an itinerary that can arrive ($\lambda^{[1,T]}_{ij}>0$) let $T_{ij}=\max\{t\le T:\lambda^t_{ij}>0\}$, and let
--
--   $$\lambda_{\min}=\min_{i\le j:\ \lambda^{[1,T]}_{ij}>0}\ \frac{\lambda^{T_{ij}}_{ij}}{T_{ij}}.$$
--
--   Then $0<\lambda_{\min}\le1$, and for every $\theta\ge1$, every itinerary that can arrive and every $t\in[\theta T_{ij}]$,
--
--   $$\lambda^{(t,\theta T_{ij}]}_{ij}(\theta)=\sum_{t'=t+1}^{\theta T_{ij}}\lambda^{t'}_{ij}(\theta)\ \ge\ \lambda_{\min}\,(\theta T_{ij}-t),$$
--
--   where $\lambda^{t'}_{ij}(\theta)=\lambda^{\lceil t'/\theta\rceil}_{ij}$ are the arrival probabilities of the $\theta$-th problem. In words, the expected demand still to come for a type is at least proportional to the time left before its last possible arrival, with a constant independent of $\theta$; the proof of Theorem 4 feeds this into Hoeffding's inequality.
--
--   Differences from the source:
--   - encoding: inf_{t,i,j: t∈[θT_ij]} λ^{(t,θT_ij]}_{ij}(θ)/(θT_ij − t) ≥ λ_min with 0/0 = 1 → λ_min·(θT_ij − t) ≤ Σ_{t'∈(t,θT_ij]} λ^{t'}_{ij}(θ) for every t ∈ [θT_ij]; reason: the inequality multiplied by θT_ij − t ≥ 0; at t = θT_ij both sides are 0, which is the 0/0 = 1 ≥ λ_min convention
--   - encoding: λ_min = inf_{i ≤ j} λ^{T_ij}_{ij}/T_ij, with T_ij ≥ 1 assumed 'without loss of generality' → minimum over the itineraries with λ^{[1,T]}_{ij} > 0; λ_min = 1 when there is none; reason: itineraries that never arrive are the ones the proof sets aside; with none the inequality is vacuous
--   - encoding: λ^t_{ij}(θ) = λ^{⌈t/θ⌉}_{ij} → lam ((t + θ − 1)/θ) i j; reason: ⌈t/θ⌉ = (t + θ − 1)/θ in ℕ for θ ≥ 1
-- source:
--   F. Zhu, S. Liu, R. Wang, Z. Wang, Assign-to-Seat: Dynamic Capacity Control for Selling High-Speed Train Tickets, Manufacturing & Service Operations Management (2023), doi:10.1287/msom.2023.1188, proof of Theorem 4, (EC.22), pp.ec21–ec22

import Mathlib
import Definitions.Def_AssignToSeatRM_Basic
import Definitions.Def_AssignToSeatRM_Dynamic

set_option autoImplicit false
open Classical
open scoped BigOperators

noncomputable section

namespace AssignToSeatRM

/-- **(EC.22)** (Zhu, Liu, Wang and Wang, *Assign-to-Seat*, MSOM 2023,
doi:10.1287/msom.2023.1188, pp.ec21–ec22): with `T_{ij} = sup{t ≤ T : λ^t_{ij} > 0}` and
`λ_min = inf_{i ≤ j} λ^{T_{ij}}_{ij} / T_{ij}` (over the itineraries that can arrive),
`inf_{t,i,j: t ∈ [θT_{ij}]} λ^{(t,θT_{ij}]}_{ij}(θ) / (θT_{ij} − t) ≥ λ_min > 0`, with
`0/0 = 1 ≥ λ_min`.

**Formalization Note.** The ratio is multiplied out: for every `θ ≥ 1`, every itinerary with
`λ^{[1,T]}_{ij} > 0` and every `t ∈ [θT_{ij}]`,
`λ_min · (θT_{ij} − t) ≤ Σ_{t' = t+1}^{θT_{ij}} λ^{t'}_{ij}(θ)`; at `t = θT_{ij}` both sides are
`0`, which is the paper's `0/0 = 1 ≥ λ_min`. The conclusion also records `λ_min ≤ 1`. -/
theorem ec22_lambda_min {M T : ℕ} (lam : ℕ → ℕ → ℕ → ℝ) (hlam : IsArrivalProb M T lam) :
    0 < lamMin M T lam ∧ lamMin M T lam ≤ 1 ∧
      ∀ θ : ℕ, 1 ≤ θ → ∀ ij ∈ arrivingTypes M T lam, ∀ t : ℕ, 1 ≤ t →
        t ≤ θ * lastArrival T lam ij.1 ij.2 →
          lamMin M T lam * (((θ * lastArrival T lam ij.1 ij.2 : ℕ) : ℝ) - t) ≤
            ∑ t' ∈ Finset.Ioc t (θ * lastArrival T lam ij.1 ij.2),
              lamScale lam θ t' ij.1 ij.2 := by sorry

end AssignToSeatRM
