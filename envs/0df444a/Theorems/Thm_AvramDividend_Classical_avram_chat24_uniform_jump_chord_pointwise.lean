-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_chat24_uniform_jump_chord_pointwise
-- name    : AvramDividend.Classical.avram_chat24_uniform_jump_chord_pointwise
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T00:23:17.192959+00:00
-- url     : https://prove2.me/theorems/bcfcb5c7-2d94-4d43-b4c7-d502cfbb1aea
-- title:
--   Uniform chord sums converge at a nonzero downward jump
-- statement:
--   Pointwise prerequisite of AE parent 7148e5e3-d521-4a02-9b16-15f9f757c1a9 at a fixed positive time t<=B with nonzero downward jump. Select the unique strict-left mesh cell. Accepted cell-path limits give V->y and m->leftLim f(t)-f(t)>0. The band and monotone-control hypotheses are retained to prove the essential domain fact y+Delta f(t)>=a>0: V-m+d*h is at least a on each selected cell. C1 regularity then gives continuity at both limiting arguments. The quotient, multiplied by the jump mass and discount, converges to the discounted payoff jump. Disjointness collapses each finite sum to that one selected cell. No parent assumption, mapped measure, summability, source identity, or integrability hypothesis is used; the dependency is independent and source-faithful.

import Mathlib
open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology

theorem AvramDividend.Classical.avram_chat24_uniform_jump_chord_pointwise
    (f K : ℝ≥0 → ℝ) (v d a b q y : ℝ) (B t : ℝ≥0)
    (hB : 0 < B) (ht : 0 < t) (htB : t ≤ B) (ha : 0 < a)
    (hfr : ContinuousWithinAt f (Ici t) t)
    (hfl : ∃ l, Tendsto f (𝓝[<] t) (nhds l))
    (hK : Monotone K)
    (hband : ∀ s : ℝ≥0, s ≤ B → v + f s - K s ∈ Icc a b)
    (hy : y ∈ Icc a b)
    (hpre : Tendsto (fun s => v + f s - K s) (𝓝[<] t) (nhds y))
    (hjump : f t - Function.leftLim f t < 0)
    (w : ℝ → ℝ) (hw : ContDiffOn ℝ 1 w (Ioi 0)) (n0 : ℕ) :
    let u : ℕ → ℕ → ℝ≥0 := fun n i => B * (i : ℝ≥0) / ((n + 1 : ℕ) : ℝ≥0)
    let h : ℕ → ℝ := fun n => (B : ℝ) / ((n + 1 : ℕ) : ℝ)
    let V : ℕ → ℕ → ℝ := fun n i => v + f (u n i) - K (u n i)
    let m : ℕ → ℕ → ℝ := fun n i => d * h n - (f (u n (i + 1)) - f (u n i))
    let F : ℕ → ℝ := fun n => if n0 ≤ n then
      ∑ i ∈ Finset.range (n + 1),
        if u n i < t ∧ t ≤ u n (i + 1) then
          Real.exp (-(q * (u n (i + 1) : ℝ))) *
            ((w (V n i - m n i) - w (V n i)) / m n i) *
              (-(f t - Function.leftLim f t)) else 0
      else 0
    Tendsto F atTop (nhds (Real.exp (-(q * (t : ℝ))) *
      (w (y + (f t - Function.leftLim f t)) - w y))) := by sorry
