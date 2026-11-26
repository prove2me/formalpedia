-- Prove2me | Theorems.Thm_BellWilliams2001_ThresholdPolicy_threshold_queue_increment_from_renewal_bounds
-- name    : BellWilliams2001.ThresholdPolicy.threshold_queue_increment_from_renewal_bounds
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-26T06:07:20.181608+00:00
-- url     : https://prove2.me/theorems/65151abb-5f46-45d8-8281-ef76cb90c62c
-- title:
--   The two drift inequalities for threshold queue increments
-- statement:
--   Suppose the three class 1 renewal primitives satisfy the prescribed uniform increment estimates. The class 1 queue then has a uniform absolute increment bound and opposing drift inequalities on intervals lying below and above the threshold. Above the threshold both servers work on class 1. Below the threshold server 2 devotes no service to class 1.
-- source:
--   Bell and Williams (2001), https://doi.org/10.1214/aoap/1015345343, Definition 5.1 and Sections 6–7, the two threshold excursion regimes

import Definitions.Def_BellWilliams2001_ThresholdPolicy_Threshold

open Set

namespace BellWilliams2001.ThresholdPolicy

theorem threshold_queue_increment_from_renewal_bounds {Ω : Type*} [MeasurableSpace Ω] (M : SystemSequence Ω)
    (c : ℝ) (n : ℕ) (T : Allocation Ω) (hA : M.IsAdmissible n T) (hP : M.IsThreshold c n T)
    (hL : 1 ≤ M.threshold c n) (ω : Ω) (H η E α : ℝ) (hη : 0 ≤ η) (hE : 0 ≤ E)
    (hPosDrift : α + 2*η ≤ M.lamR n 0 - M.muR n 0)
    (hNegDrift : α + 3*η ≤ M.muR n 0 + M.muR n 1 - M.lamR n 0)
    (hArr : ∀ a b, 0 ≤ a → a ≤ b → b ≤ H →
      |M.A n 0 ω b - M.A n 0 ω a - M.lamR n 0 * (b-a)| ≤ η*(b-a) + E)
    (hServ : ∀ j : Fin 3, j ≠ 2 → ∀ a b, 0 ≤ a → a ≤ b → b ≤ H →
      |M.S n j ω b - M.S n j ω a - M.muR n j * (b-a)| ≤ η*(b-a) + E) :
    let q := M.queue n T ω 0
    let L : ℝ := M.threshold c n
    let K := M.lamR n 0 + M.muR n 0 + M.muR n 1 + 3*η
    (∀ a b, 0 ≤ a → a ≤ b → b ≤ H → |q b-q a| ≤ K*(b-a)+3*E) ∧
    (∀ a b, 0 ≤ a → a ≤ b → b ≤ H → (∀ s ∈ Ioc a b, q s ≤ L) → α*(b-a)-3*E ≤ q b-q a) ∧
    (∀ a b, 0 ≤ a → a ≤ b → b ≤ H → (∀ s ∈ Ioc a b, L < q s) → q b-q a ≤ -α*(b-a)+3*E) := by sorry

end BellWilliams2001.ThresholdPolicy
