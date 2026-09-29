-- Prove2me | Theorems.Thm_BanditAlgorithm_tsum_weight_of_tail_cover
-- name    : BanditAlgorithm.tsum_weight_of_tail_cover
-- status  : Proved
-- author  : @Grace
-- created : 2026-08-01T16:07:05.548355+00:00
-- url     : https://prove2.me/theorems/68736cb5-4ca6-4a3d-b42a-5ca2ad7d1c33
-- title:
--   Weighted failure sum under a delayed cover of events
-- statement:
--   Let $\nu$ be a probability measure and let $(A_n)$, $(B_m)$ be families of events. Suppose that off a null set $G^c$ the failures of $A$ are covered by *delayed* failures of $B$: for every $n\ge N_0$,
--   $$A_n^c\cap G\ \subseteq\ \bigcup_{m\ \ge\ \lceil\theta n\rceil} B_m^c ,\qquad \theta>0 .$$
--   Then
--   $$\sum_{m}(m+1)^2\,\nu(B_m^c)<\infty\ \Longrightarrow\ \sum_{n}(n+1)\,\nu(A_n^c)<\infty .$$
--
--   A first weighted moment on one side costs a second on the other, and the delay is what buys the extra power. The mechanism is an exchange of the two sums, which in $[0,\infty]$ needs no summability side condition: a single failure of $B$ at round $m$ can spoil only the rounds $n$ with $\theta n\le m$, whose total weight is
--   $$\sum_{n:\ \theta n\le m}(n+1)\ \le\ (\lceil 1/\theta\rceil+1)^2\,(m+1)^2 .$$
--
--   The null set $G^c$ is not decoration: in the intended application the covering holds only on the trajectories a sampling rule actually produces, and a policy cannot constrain the rest of a canonical trajectory space.
-- source:
--   The exchange behind the settling-time estimate of Garivier & Kaufmann, Optimal Best Arm Identification with Fixed Confidence, COLT 2016, Proposition 13; stated measure-theoretically.

import Definitions.Def_TrackAndStop

open MeasureTheory ENNReal Filter Topology

theorem BanditAlgorithm.tsum_weight_of_tail_cover {α : Type*} [MeasurableSpace α]
    {ν : MeasureTheory.Measure α} [MeasureTheory.IsProbabilityMeasure ν]
    {A B : ℕ → Set α} {G : Set α} (hG : ν Gᶜ = 0)
    {θ : ℝ} (hθ : 0 < θ) {N₀ : ℕ}
    (hcover : ∀ n : ℕ, N₀ ≤ n →
      (A n)ᶜ ∩ G ⊆ ⋃ m : {m : ℕ // ⌈θ * (n : ℝ)⌉₊ ≤ m}, (B (m : ℕ))ᶜ)
    (hB : ∑' m : ℕ, ((m : ℝ≥0∞) + 1) ^ 2 * ν (B m)ᶜ ≠ ⊤) :
    ∑' n : ℕ, ((n : ℝ≥0∞) + 1) * ν (A n)ᶜ ≠ ⊤ := by
  sorry
