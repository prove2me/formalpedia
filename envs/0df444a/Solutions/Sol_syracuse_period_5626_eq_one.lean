-- Prove2me | solution 1 for syracuse_period_5626_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @FakeMink
-- created : 2026-10-01T15:44:02.721889+00:00
-- url     : https://prove2.me/submissions/54a00adc-e9c9-43f9-9106-81c8fe970a92

import Mathlib
import Definitions.Def_syracuseStep
import Theorems.Thm_syracuse_no_cycle_below_2310000

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 200000

open scoped BigOperators

universe u

/- Newly assembled proof candidate. No local compilation has been run.
The fixed5626 target is distinct from the still-Open unbounded cycle parent.
All source-only component files are preserved unchanged. -/


/- Component: cycle_four_window_products_draft_01.lean -/
/-
Uncompiled research draft: no machine-verification claim is made.
The declarations are private and confined to a dedicated draft namespace.
This file contains only polynomial AM-GM and finite-permutation product helpers;
no reciprocal-case bounds, Syracuse instantiation, or cycle criterion is included.
-/


namespace CollatzFourWindowProductsDraft01

private theorem amgm4_bound {a b c d L : ℚ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hL : 0 ≤ L) (hsum : a + b + c + d ≤ 4 * L) :
    a * b * c * d ≤ L ^ 4 := by
  have hab : 4 * a * b ≤ (a + b) ^ 2 := four_mul_le_sq_add a b
  have hcd : 4 * c * d ≤ (c + d) ^ 2 := four_mul_le_sq_add c d
  have hpairs : 4 * (a + b) * (c + d) ≤ (a + b + c + d) ^ 2 := by
    simpa only [add_assoc] using four_mul_le_sq_add (a + b) (c + d)
  have hmul : (4 * a * b) * (4 * c * d) ≤ (a + b) ^ 2 * (c + d) ^ 2 :=
    mul_le_mul hab hcd (by positivity) (sq_nonneg (a + b))
  have hscaled :
      16 * ((4 * a * b) * (4 * c * d)) ≤
        16 * ((a + b) ^ 2 * (c + d) ^ 2) :=
    mul_le_mul_of_nonneg_left hmul (by norm_num)
  have hsquare :
      (4 * (a + b) * (c + d)) ^ 2 ≤ ((a + b + c + d) ^ 2) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hpairs 2
  have hquartic : 256 * (a * b * c * d) ≤ (a + b + c + d) ^ 4 := by
    calc
      256 * (a * b * c * d) = 16 * ((4 * a * b) * (4 * c * d)) := by ring
      _ ≤ 16 * ((a + b) ^ 2 * (c + d) ^ 2) := hscaled
      _ = (4 * (a + b) * (c + d)) ^ 2 := by ring
      _ ≤ ((a + b + c + d) ^ 2) ^ 2 := hsquare
      _ = (a + b + c + d) ^ 4 := by ring
  have hsumPow : (a + b + c + d) ^ 4 ≤ (4 * L) ^ 4 :=
    pow_le_pow_left₀ (by positivity) hsum 4
  have hfinal : 256 * (a * b * c * d) ≤ 256 * L ^ 4 := by
    calc
      256 * (a * b * c * d) ≤ (a + b + c + d) ^ 4 := hquartic
      _ ≤ (4 * L) ^ 4 := hsumPow
      _ = 256 * L ^ 4 := by ring
  nlinarith only [hfinal]

private theorem window_product_bound {ι : Type u} [Fintype ι]
    (R : Equiv.Perm ι) (F : ι → ℚ) (L : ℚ)
    (hF : ∀ i : ι, 0 ≤ F i) (hL : 0 ≤ L)
    (hwindow : ∀ i : ι,
      F i * F (R i) * F (R (R i)) * F (R (R (R i))) ≤ L ^ 4) :
    (∏ i : ι, F i) ≤ L ^ (Fintype.card ι) := by
  classical
  let P : ℚ := ∏ i : ι, F i
  have hP : 0 ≤ P := by
    dsimp [P]
    exact Finset.prod_nonneg (fun i _ => hF i)
  have hR1 : (∏ i : ι, F (R i)) = P := Equiv.prod_comp R F
  have hR2 : (∏ i : ι, F (R (R i))) = P :=
    (Equiv.prod_comp R (fun i : ι => F (R i))).trans hR1
  have hR3 : (∏ i : ι, F (R (R (R i)))) = P :=
    (Equiv.prod_comp R (fun i : ι => F (R (R i)))).trans hR2
  have hprod :
      (∏ i : ι, F i * F (R i) * F (R (R i)) * F (R (R (R i)))) ≤
        (∏ _i : ι, L ^ 4) := by
    apply Finset.prod_le_prod
    · intro i _
      exact mul_nonneg
        (mul_nonneg (mul_nonneg (hF i) (hF (R i))) (hF (R (R i))))
        (hF (R (R (R i))))
    · intro i _
      exact hwindow i
  have hleft :
      (∏ i : ι, F i * F (R i) * F (R (R i)) * F (R (R (R i)))) = P ^ 4 := by
    simp only [Finset.prod_mul_distrib, hR1, hR2, hR3]
    change P * P * P * P = P ^ 4
    ring
  have hright : (∏ _i : ι, L ^ 4) = (L ^ (Fintype.card ι)) ^ 4 := by
    simp only [Finset.prod_const, Finset.card_univ]
    rw [← pow_mul, ← pow_mul, Nat.mul_comm]
  have hfour : P ^ 4 ≤ (L ^ (Fintype.card ι)) ^ 4 := by
    calc
      P ^ 4 = (∏ i : ι, F i * F (R i) * F (R (R i)) * F (R (R (R i)))) :=
        hleft.symm
      _ ≤ (∏ _i : ι, L ^ 4) := hprod
      _ = (L ^ (Fintype.card ι)) ^ 4 := hright
  exact (pow_le_pow_iff_left₀ hP (pow_nonneg hL _) (by decide : (4 : ℕ) ≠ 0)).mp hfour

end CollatzFourWindowProductsDraft01

/- Component: cycle_four_state_reciprocal_draft_01.lean -/
/-
Uncompiled, source-only research draft. No machine-verification claim is made.
The transition relation is rational: its high branch is an inequality, not an
assumed equality or a fixed valuation. No positivity, oddness, or integrality
shortcut is used beyond the explicitly stated rational lower bounds.

The 27 coefficient choices below implement the independently assessed finite
hand argument. Every choice is accompanied by ordinary linarith proofs of its
four affine lower bounds and a norm_num proof of its reciprocal coefficient
sum. The generator supplies proof text only; no generated numeric fact is
trusted, and no native evaluator, admission, or custom axiom is used.
-/

namespace CollatzFourStateReciprocalDraft01

/-- Exact low branches, or a conservative high-valuation backwards inequality. -/
def edge (x y : ℚ) : Prop :=
  2 * y = 3 * x + 1 ∨ 4 * y = 3 * x + 1 ∨ 8 * y ≤ 3 * x + 1

private theorem reciprocal_from_lower {D r x : ℚ}
    (hD : 0 < D) (hr : 0 < r) (hx : r * D ≤ x) :
    1 / x ≤ (1 / r) / D := by
  simpa only [div_div] using one_div_le_one_div_of_le (mul_pos hr hD) hx

private theorem reciprocal_sum_of_coefficients
    {D x0 x1 x2 x3 r0 r1 r2 r3 : ℚ}
    (hD : 0 < D)
    (hr0 : 0 < r0) (hr1 : 0 < r1) (hr2 : 0 < r2) (hr3 : 0 < r3)
    (h0 : r0 * D ≤ x0) (h1 : r1 * D ≤ x1)
    (h2 : r2 * D ≤ x2) (h3 : r3 * D ≤ x3)
    (hsum : 1 / r0 + 1 / r1 + 1 / r2 + 1 / r3 ≤ (119 : ℚ) / 36) :
    1 / x0 + 1 / x1 + 1 / x2 + 1 / x3 ≤ ((119 : ℚ) / 36) / D := by
  have q0 : 1 / x0 ≤ (1 / r0) / D := reciprocal_from_lower hD hr0 h0
  have q1 : 1 / x1 ≤ (1 / r1) / D := reciprocal_from_lower hD hr1 h1
  have q2 : 1 / x2 ≤ (1 / r2) / D := reciprocal_from_lower hD hr2 h2
  have q3 : 1 / x3 ≤ (1 / r3) / D := reciprocal_from_lower hD hr3 h3
  calc
    1 / x0 + 1 / x1 + 1 / x2 + 1 / x3 ≤
        (1 / r0) / D + (1 / r1) / D + (1 / r2) / D + (1 / r3) / D :=
      add_le_add (add_le_add (add_le_add q0 q1) q2) q3
    _ = (1 / r0 + 1 / r1 + 1 / r2 + 1 / r3) / D := by ring
    _ ≤ ((119 : ℚ) / 36) / D := div_le_div_of_nonneg_right hsum (le_of_lt hD)

/-- Generic rational four-state bound; no Syracuse or parity assumption is hidden. -/
theorem four_state_reciprocal_bound {B x0 x1 x2 x3 : ℚ}
    (hB : 2 < B)
    (hx0 : B ≤ x0) (hx1 : B ≤ x1) (hx2 : B ≤ x2) (hx3 : B ≤ x3)
    (h01 : edge x0 x1) (h12 : edge x1 x2) (h23 : edge x2 x3) :
    1 / x0 + 1 / x1 + 1 / x2 + 1 / x3 ≤ 119 / (36 * (B - 2)) := by
  have hD : 0 < B - 2 := by linarith only [hB]
  unfold edge at h01 h12 h23
  have hbound :
      1 / x0 + 1 / x1 + 1 / x2 + 1 / x3 ≤ ((119 : ℚ) / 36) / (B - 2) := by
    rcases h01 with h01 | h01 | h01
    all_goals rcases h12 with h12 | h12 | h12
    all_goals rcases h23 with h23 | h23 | h23
    -- Pattern 111; H means only the stated high inequality.
    · apply reciprocal_sum_of_coefficients
        (r0 := (1 : ℚ)) (r1 := (3 / 2 : ℚ)) (r2 := (9 / 4 : ℚ)) (r3 := (27 / 8 : ℚ)) hD
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · linarith only [hB, hx0, hx1, hx2, hx3, h01, h12, h23]
      · linarith only [hB, hx0, hx1, hx2, hx3, h01, h12, h23]
      · linarith only [hB, hx0, hx1, hx2, hx3, h01, h12, h23]
      · linarith only [hB, hx0, hx1, hx2, hx3, h01, h12, h23]
      · norm_num
    -- Pattern 112; H means only the stated high inequality.
    · apply reciprocal_sum_of_coefficients
        (r0 := (1 : ℚ)) (r1 := (3 / 2 : ℚ)) (r2 := (9 / 4 : ℚ)) (r3 := (27 / 16 : ℚ)) hD
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · linarith only [hB, hx0, hx1, hx2, hx3, h01, h12, h23]
      · linarith only [hB, hx0, hx1, hx2, hx3, h01, h12, h23]
      · linarith only [hB, hx0, hx1, hx2, hx3, h01, h12, h23]
      · linarith only [hB, hx0, hx1, hx2, hx3, h01, h12, h23]
      · norm_num
    -- Pattern 11H; H means only the stated high inequality.
    · apply reciprocal_sum_of_coefficients
        (r0 := (32 / 27 : ℚ)) (r1 := (16 / 9 : ℚ)) (r2 := (8 / 3 : ℚ)) (r3 := (1 : ℚ)) hD
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · linarith only [hB, hx0, hx1, hx2, hx3, h01, h12, h23]
      · linarith only [hB, hx0, hx1, hx2, hx3, h01, h12, h23]
      · linarith only [hB, hx0, hx1, hx2, hx3, h01, h12, h23]
      · linarith only [hB, hx0, hx1, hx2, hx3, h01, h12, h23]
      · norm_num
    -- Pattern 121; H means only the stated high inequality.
    · apply reciprocal_sum_of_coefficients
        (r0 := (1 : ℚ)) (r1 := (3 / 2 : ℚ)) (r2 := (9 / 8 : ℚ)) (r3 := (27 / 16 : ℚ)) hD
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · linarith only [hB, hx0, hx1, hx2, hx3, h01, h12, h23]
      · linarith only [hB, hx0, hx1, hx2, hx3, h01, h12, h23]
      · linarith only [hB, hx0, hx1, hx2, hx3, h01, h12, h23]
      · linarith only [hB, hx0, hx1, hx2, hx3, h01, h12, h23]
      · norm_num
    -- Pattern 122; H means only the stated high inequality.
    · apply reciprocal_sum_of_coefficients
        (r0 := (32 / 27 : ℚ)) (r1 := (16 / 9 : ℚ)) (r2 := (4 / 3 : ℚ)) (r3 := (1 : ℚ)) hD
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · linarith only [hB, hx0, hx1, hx2, hx3, h01, h12, h23]
      · linarith only [hB, hx0, hx1, hx2, hx3, h01, h12, h23]
      · linarith only [hB, hx0, hx1, hx2, hx3, h01, h12, h23]
      · linarith only [hB, hx0, hx1, hx2, hx3, h01, h12, h23]
      · norm_num
    -- Pattern 12H; H means only the stated high inequality.
    · apply reciprocal_sum_of_coefficients
        (r0 := (32 / 27 : ℚ)) (r1 := (16 / 9 : ℚ)) (r2 := (8 / 3 : ℚ)) (r3 := (1 : ℚ)) hD
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · linarith only [hB, hx0, hx1, hx2, hx3, h01, h12, h23]
      · linarith only [hB, hx0, hx1, hx2, hx3, h01, h12, h23]
      · linarith only [hB, hx0, hx1, hx2, hx3, h01, h12, h23]
      · linarith only [hB, hx0, hx1, hx2, hx3, h01, h12, h23]
      · norm_num
    -- Pattern 1H1; H means only the stated high inequality.
    · apply reciprocal_sum_of_coefficients
        (r0 := (16 / 9 : ℚ)) (r1 := (8 / 3 : ℚ)) (r2 := (1 : ℚ)) (r3 := (3 / 2 : ℚ)) hD
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · linarith only [hB, hx0, hx1, hx2, hx3, h01, h12, h23]
      · linarith only [hB, hx0, hx1, hx2, hx3, h01, h12, h23]
      · linarith only [hB, hx0, hx1, hx2, hx3, h01, h12, h23]
      · linarith only [hB, hx0, hx1, hx2, hx3, h01, h12, h23]
      · norm_num
    -- Pattern 1H2; H means only the stated high inequality.
    · apply reciprocal_sum_of_coefficients
        (r0 := (16 / 9 : ℚ)) (r1 := (8 / 3 : ℚ)) (r2 := (4 / 3 : ℚ)) (r3 := (1 : ℚ)) hD
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · linarith only [hB, hx0, hx1, hx2, hx3, h01, h12, h23]
      · linarith only [hB, hx0, hx1, hx2, hx3, h01, h12, h23]
      · linarith only [hB, hx0, hx1, hx2, hx3, h01, h12, h23]
      · linarith only [hB, hx0, hx1, hx2, hx3, h01, h12, h23]
      · norm_num
    -- Pattern 1HH; H means only the stated high inequality.
    · apply reciprocal_sum_of_coefficients
        (r0 := (1 : ℚ)) (r1 := (8 / 3 : ℚ)) (r2 := (8 / 3 : ℚ)) (r3 := (1 : ℚ)) hD
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · linarith only [hB, hx0, hx1, hx2, hx3, h01, h12, h23]
      · linarith only [hB, hx0, hx1, hx2, hx3, h01, h12, h23]
      · linarith only [hB, hx0, hx1, hx2, hx3, h01, h12, h23]
      · linarith only [hB, hx0, hx1, hx2, hx3, h01, h12, h23]
      · norm_num
    -- Pattern 211; H means only the stated high inequality.
    · apply reciprocal_sum_of_coefficients
        (r0 := (4 / 3 : ℚ)) (r1 := (1 : ℚ)) (r2 := (3 / 2 : ℚ)) (r3 := (9 / 4 : ℚ)) hD
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · linarith only [hB, hx0, hx1, hx2, hx3, h01, h12, h23]
      · linarith only [hB, hx0, hx1, hx2, hx3, h01, h12, h23]
      · linarith only [hB, hx0, hx1, hx2, hx3, h01, h12, h23]
      · linarith only [hB, hx0, hx1, hx2, hx3, h01, h12, h23]
      · norm_num
    -- Pattern 212; H means only the stated high inequality.
    · apply reciprocal_sum_of_coefficients
        (r0 := (4 / 3 : ℚ)) (r1 := (1 : ℚ)) (r2 := (3 / 2 : ℚ)) (r3 := (9 / 8 : ℚ)) hD
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · linarith only [hB, hx0, hx1, hx2, hx3, h01, h12, h23]
      · linarith only [hB, hx0, hx1, hx2, hx3, h01, h12, h23]
      · linarith only [hB, hx0, hx1, hx2, hx3, h01, h12, h23]
      · linarith only [hB, hx0, hx1, hx2, hx3, h01, h12, h23]
      · norm_num
    -- Pattern 21H; H means only the stated high inequality.
    · apply reciprocal_sum_of_coefficients
        (r0 := (32 / 27 : ℚ)) (r1 := (16 / 9 : ℚ)) (r2 := (8 / 3 : ℚ)) (r3 := (1 : ℚ)) hD
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · linarith only [hB, hx0, hx1, hx2, hx3, h01, h12, h23]
      · linarith only [hB, hx0, hx1, hx2, hx3, h01, h12, h23]
      · linarith only [hB, hx0, hx1, hx2, hx3, h01, h12, h23]
      · linarith only [hB, hx0, hx1, hx2, hx3, h01, h12, h23]
      · norm_num
    -- Pattern 221; H means only the stated high inequality.
    · apply reciprocal_sum_of_coefficients
        (r0 := (16 / 9 : ℚ)) (r1 := (4 / 3 : ℚ)) (r2 := (1 : ℚ)) (r3 := (3 / 2 : ℚ)) hD
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · linarith only [hB, hx0, hx1, hx2, hx3, h01, h12, h23]
      · linarith only [hB, hx0, hx1, hx2, hx3, h01, h12, h23]
      · linarith only [hB, hx0, hx1, hx2, hx3, h01, h12, h23]
      · linarith only [hB, hx0, hx1, hx2, hx3, h01, h12, h23]
      · norm_num
    -- Pattern 222; H means only the stated high inequality.
    · apply reciprocal_sum_of_coefficients
        (r0 := (64 / 27 : ℚ)) (r1 := (16 / 9 : ℚ)) (r2 := (4 / 3 : ℚ)) (r3 := (1 : ℚ)) hD
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · linarith only [hB, hx0, hx1, hx2, hx3, h01, h12, h23]
      · linarith only [hB, hx0, hx1, hx2, hx3, h01, h12, h23]
      · linarith only [hB, hx0, hx1, hx2, hx3, h01, h12, h23]
      · linarith only [hB, hx0, hx1, hx2, hx3, h01, h12, h23]
      · norm_num
    -- Pattern 22H; H means only the stated high inequality.
    · apply reciprocal_sum_of_coefficients
        (r0 := (32 / 27 : ℚ)) (r1 := (16 / 9 : ℚ)) (r2 := (8 / 3 : ℚ)) (r3 := (1 : ℚ)) hD
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · linarith only [hB, hx0, hx1, hx2, hx3, h01, h12, h23]
      · linarith only [hB, hx0, hx1, hx2, hx3, h01, h12, h23]
      · linarith only [hB, hx0, hx1, hx2, hx3, h01, h12, h23]
      · linarith only [hB, hx0, hx1, hx2, hx3, h01, h12, h23]
      · norm_num
    -- Pattern 2H1; H means only the stated high inequality.
    · apply reciprocal_sum_of_coefficients
        (r0 := (16 / 9 : ℚ)) (r1 := (8 / 3 : ℚ)) (r2 := (1 : ℚ)) (r3 := (3 / 2 : ℚ)) hD
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · linarith only [hB, hx0, hx1, hx2, hx3, h01, h12, h23]
      · linarith only [hB, hx0, hx1, hx2, hx3, h01, h12, h23]
      · linarith only [hB, hx0, hx1, hx2, hx3, h01, h12, h23]
      · linarith only [hB, hx0, hx1, hx2, hx3, h01, h12, h23]
      · norm_num
    -- Pattern 2H2; H means only the stated high inequality.
    · apply reciprocal_sum_of_coefficients
        (r0 := (16 / 9 : ℚ)) (r1 := (8 / 3 : ℚ)) (r2 := (4 / 3 : ℚ)) (r3 := (1 : ℚ)) hD
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · linarith only [hB, hx0, hx1, hx2, hx3, h01, h12, h23]
      · linarith only [hB, hx0, hx1, hx2, hx3, h01, h12, h23]
      · linarith only [hB, hx0, hx1, hx2, hx3, h01, h12, h23]
      · linarith only [hB, hx0, hx1, hx2, hx3, h01, h12, h23]
      · norm_num
    -- Pattern 2HH; H means only the stated high inequality.
    · apply reciprocal_sum_of_coefficients
        (r0 := (1 : ℚ)) (r1 := (8 / 3 : ℚ)) (r2 := (8 / 3 : ℚ)) (r3 := (1 : ℚ)) hD
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · linarith only [hB, hx0, hx1, hx2, hx3, h01, h12, h23]
      · linarith only [hB, hx0, hx1, hx2, hx3, h01, h12, h23]
      · linarith only [hB, hx0, hx1, hx2, hx3, h01, h12, h23]
      · linarith only [hB, hx0, hx1, hx2, hx3, h01, h12, h23]
      · norm_num
    -- Pattern H11; H means only the stated high inequality.
    · apply reciprocal_sum_of_coefficients
        (r0 := (8 / 3 : ℚ)) (r1 := (1 : ℚ)) (r2 := (3 / 2 : ℚ)) (r3 := (9 / 4 : ℚ)) hD
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · linarith only [hB, hx0, hx1, hx2, hx3, h01, h12, h23]
      · linarith only [hB, hx0, hx1, hx2, hx3, h01, h12, h23]
      · linarith only [hB, hx0, hx1, hx2, hx3, h01, h12, h23]
      · linarith only [hB, hx0, hx1, hx2, hx3, h01, h12, h23]
      · norm_num
    -- Pattern H12; H means only the stated high inequality.
    · apply reciprocal_sum_of_coefficients
        (r0 := (8 / 3 : ℚ)) (r1 := (1 : ℚ)) (r2 := (3 / 2 : ℚ)) (r3 := (9 / 8 : ℚ)) hD
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · linarith only [hB, hx0, hx1, hx2, hx3, h01, h12, h23]
      · linarith only [hB, hx0, hx1, hx2, hx3, h01, h12, h23]
      · linarith only [hB, hx0, hx1, hx2, hx3, h01, h12, h23]
      · linarith only [hB, hx0, hx1, hx2, hx3, h01, h12, h23]
      · norm_num
    -- Pattern H1H; H means only the stated high inequality.
    · apply reciprocal_sum_of_coefficients
        (r0 := (8 / 3 : ℚ)) (r1 := (1 : ℚ)) (r2 := (8 / 3 : ℚ)) (r3 := (1 : ℚ)) hD
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · linarith only [hB, hx0, hx1, hx2, hx3, h01, h12, h23]
      · linarith only [hB, hx0, hx1, hx2, hx3, h01, h12, h23]
      · linarith only [hB, hx0, hx1, hx2, hx3, h01, h12, h23]
      · linarith only [hB, hx0, hx1, hx2, hx3, h01, h12, h23]
      · norm_num
    -- Pattern H21; H means only the stated high inequality.
    · apply reciprocal_sum_of_coefficients
        (r0 := (8 / 3 : ℚ)) (r1 := (4 / 3 : ℚ)) (r2 := (1 : ℚ)) (r3 := (3 / 2 : ℚ)) hD
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · linarith only [hB, hx0, hx1, hx2, hx3, h01, h12, h23]
      · linarith only [hB, hx0, hx1, hx2, hx3, h01, h12, h23]
      · linarith only [hB, hx0, hx1, hx2, hx3, h01, h12, h23]
      · linarith only [hB, hx0, hx1, hx2, hx3, h01, h12, h23]
      · norm_num
    -- Pattern H22; H means only the stated high inequality.
    · apply reciprocal_sum_of_coefficients
        (r0 := (8 / 3 : ℚ)) (r1 := (16 / 9 : ℚ)) (r2 := (4 / 3 : ℚ)) (r3 := (1 : ℚ)) hD
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · linarith only [hB, hx0, hx1, hx2, hx3, h01, h12, h23]
      · linarith only [hB, hx0, hx1, hx2, hx3, h01, h12, h23]
      · linarith only [hB, hx0, hx1, hx2, hx3, h01, h12, h23]
      · linarith only [hB, hx0, hx1, hx2, hx3, h01, h12, h23]
      · norm_num
    -- Pattern H2H; H means only the stated high inequality.
    · apply reciprocal_sum_of_coefficients
        (r0 := (8 / 3 : ℚ)) (r1 := (1 : ℚ)) (r2 := (8 / 3 : ℚ)) (r3 := (1 : ℚ)) hD
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · linarith only [hB, hx0, hx1, hx2, hx3, h01, h12, h23]
      · linarith only [hB, hx0, hx1, hx2, hx3, h01, h12, h23]
      · linarith only [hB, hx0, hx1, hx2, hx3, h01, h12, h23]
      · linarith only [hB, hx0, hx1, hx2, hx3, h01, h12, h23]
      · norm_num
    -- Pattern HH1; H means only the stated high inequality.
    · apply reciprocal_sum_of_coefficients
        (r0 := (8 / 3 : ℚ)) (r1 := (8 / 3 : ℚ)) (r2 := (1 : ℚ)) (r3 := (1 : ℚ)) hD
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · linarith only [hB, hx0, hx1, hx2, hx3, h01, h12, h23]
      · linarith only [hB, hx0, hx1, hx2, hx3, h01, h12, h23]
      · linarith only [hB, hx0, hx1, hx2, hx3, h01, h12, h23]
      · linarith only [hB, hx0, hx1, hx2, hx3, h01, h12, h23]
      · norm_num
    -- Pattern HH2; H means only the stated high inequality.
    · apply reciprocal_sum_of_coefficients
        (r0 := (8 / 3 : ℚ)) (r1 := (8 / 3 : ℚ)) (r2 := (1 : ℚ)) (r3 := (1 : ℚ)) hD
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · linarith only [hB, hx0, hx1, hx2, hx3, h01, h12, h23]
      · linarith only [hB, hx0, hx1, hx2, hx3, h01, h12, h23]
      · linarith only [hB, hx0, hx1, hx2, hx3, h01, h12, h23]
      · linarith only [hB, hx0, hx1, hx2, hx3, h01, h12, h23]
      · norm_num
    -- Pattern HHH; H means only the stated high inequality.
    · apply reciprocal_sum_of_coefficients
        (r0 := (8 / 3 : ℚ)) (r1 := (8 / 3 : ℚ)) (r2 := (8 / 3 : ℚ)) (r3 := (1 : ℚ)) hD
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · linarith only [hB, hx0, hx1, hx2, hx3, h01, h12, h23]
      · linarith only [hB, hx0, hx1, hx2, hx3, h01, h12, h23]
      · linarith only [hB, hx0, hx1, hx2, hx3, h01, h12, h23]
      · linarith only [hB, hx0, hx1, hx2, hx3, h01, h12, h23]
      · norm_num
  simpa only [div_div] using hbound

end CollatzFourStateReciprocalDraft01

/- Component: cycle_syracuse_transition_bridge_draft_01.lean -/
/-
Uncompiled source-only draft: no machine-verification claim is made.

Provenance:
* step_odd is copied, with its name changed, from stepOdd in the accepted
  small-cycle artifact cached in collatz-small-cycle-accepted-source.json,
  submission 0c060341-49d9-4b35-ae65-ebd77d19173e (content lines 40-43).
* step_factorization is copied from the checked local source
  prove2me_workspace/Solutions/CollatzCycleCriterion.lean, lines 18-20.

This bridge contains no finite baseline implementation, reciprocal-case proof,
cycle criterion, homogeneous approximation, or claim that the high branch is
an exact valuation. Its final statement is the bare rational three-way Or.
-/

namespace CollatzSyracuseTransitionBridgeDraft01

/-- Every accelerated image is odd, including images of even inputs. -/
theorem step_odd (n : ℕ) : Odd (syracuseStep n) := by
  rw [Nat.odd_iff, ← Nat.not_even_iff]
  intro he
  exact Nat.not_dvd_ordCompl Nat.prime_two (by omega : 3 * n + 1 ≠ 0) he.two_dvd

/-- A point with a positive return time is an image of the accelerated map. -/
theorem periodic_point_odd (n p : ℕ) (hp : 0 < p)
    (hcycle : syracuseStep^[p] n = n) : Odd n := by
  obtain ⟨q, rfl⟩ : ∃ q : ℕ, p = q + 1 := ⟨p - 1, by omega⟩
  rw [← hcycle, Function.iterate_succ_apply']
  exact step_odd _

/-- The exact defining odd-part factorization, before casting to rationals. -/
theorem step_factorization (n : ℕ) :
    2 ^ ((3 * n + 1).factorization 2) * syracuseStep n = 3 * n + 1 := by
  exact Nat.ordProj_mul_ordCompl_eq_self (3 * n + 1) 2

/-- The exact low branches and a conservative high branch needed by the rational
four-state lemma. Oddness of the input is essential to exclude exponent zero. -/
theorem step_rational_edge (n : ℕ) (hn : Odd n) :
    (2 : ℚ) * (syracuseStep n : ℚ) = 3 * (n : ℚ) + 1 ∨
    (4 : ℚ) * (syracuseStep n : ℚ) = 3 * (n : ℚ) + 1 ∨
    (8 : ℚ) * (syracuseStep n : ℚ) ≤ 3 * (n : ℚ) + 1 := by
  let e : ℕ := (3 * n + 1).factorization 2
  have hfactor : 2 ^ e * syracuseStep n = 3 * n + 1 := step_factorization n
  have hepos : 1 ≤ e := by
    by_contra h
    have hezero : e = 0 := by omega
    have hstep : syracuseStep n = 3 * n + 1 := by
      simpa only [hezero, pow_zero, one_mul] using hfactor
    have hnmod : n % 2 = 1 := Nat.odd_iff.mp hn
    have heven : (3 * n + 1) % 2 = 0 := by omega
    have hodd : (syracuseStep n) % 2 = 1 := Nat.odd_iff.mp (step_odd n)
    rw [hstep] at hodd
    omega
  by_cases heone : e = 1
  · left
    have hnat : 2 * syracuseStep n = 3 * n + 1 := by
      simpa only [heone, pow_one] using hfactor
    exact_mod_cast hnat
  · by_cases hetwo : e = 2
    · right
      left
      have hpowtwo : (2 : ℕ) ^ 2 = 4 := by norm_num
      have hnat : 4 * syracuseStep n = 3 * n + 1 := by
        simpa only [hetwo, hpowtwo] using hfactor
      exact_mod_cast hnat
    · right
      right
      have hethree : 3 ≤ e := by omega
      have hpow : (8 : ℕ) ≤ 2 ^ e := by
        calc
          (8 : ℕ) = 2 ^ 3 := by norm_num
          _ ≤ 2 ^ e := Nat.pow_le_pow_right (by decide) hethree
      have hnat : 8 * syracuseStep n ≤ 3 * n + 1 := by
        calc
          8 * syracuseStep n ≤ 2 ^ e * syracuseStep n :=
            Nat.mul_le_mul_right (syracuseStep n) hpow
          _ = 3 * n + 1 := hfactor
      exact_mod_cast hnat

end CollatzSyracuseTransitionBridgeDraft01

/- Component: cycle_two_threshold_criterion_draft_01.lean -/
/-
UNCOMPILED SOURCE-ONLY RESEARCH DRAFT.
No machine-verification or open-frontier proof is claimed by this file.

This draft separates three obligations: small-cycle exclusion below B, a
cycle-factor product upper bound at C for cycles whose inputs are at least B,
and an arbitrary-exponent arithmetic margin at C. It NEVER assumes small-cycle
exclusion below C, nor that the cycle inputs themselves are at least C.

Only needed generic facts are flattened from the previously checked sources:
Solutions/CollatzCycleTools.lean (positivity of iterates, periodicity of reached
points, and reaching the fixed point one), and Solutions/CollatzCycleCriterion.lean
(the one-step odd-part factorization). The fixed-point proof uses the checked
Nat.ordCompl_pow_mul_of_not_dvd signature from CollatzCertificateLemmas.lean.
No Solutions module, finite trajectory band, target, or Open theorem is imported.
The source component remains unchanged; its product helpers are used below in this assembly.

Source signatures were inspected under Mathlib
0df444a360eaa60ab8c11dca51a86af692955474 / Lean v4.33.1.
Actual elaboration, tactic success, and kernel checking remain unperformed.
-/

open scoped BigOperators


namespace CollatzTwoThresholdCriterionDraft01

/-- The exact telescoping product for any finite permutation of positive
rational states. Empty index types are allowed: both sides are then one. -/
theorem cycle_factor_product {ι : Type u} [Fintype ι]
    (R : Equiv.Perm ι) (x : ι → ℚ) (e : ι → ℕ)
    (hx : ∀ i : ι, 0 < x i)
    (hedge : ∀ i : ι, (2 : ℚ) ^ e i * x (R i) = 3 * x i + 1) :
    (∏ i : ι, (3 + 1 / x i)) = (2 : ℚ) ^ (∑ i : ι, e i) := by
  classical
  have hfactor (i : ι) :
      (3 + 1 / x i) = ((2 : ℚ) ^ e i * x (R i)) / x i := by
    apply (eq_div_iff (ne_of_gt (hx i))).2
    calc
      (3 + 1 / x i) * x i = 3 * x i + 1 := by
        field_simp [ne_of_gt (hx i)] <;> ring
      _ = (2 : ℚ) ^ e i * x (R i) := (hedge i).symm
  have hprod_ne : (∏ i : ι, x i) ≠ 0 :=
    ne_of_gt (Finset.prod_pos (fun i _ => hx i))
  have hpow : (∏ i : ι, (2 : ℚ) ^ e i) =
      (2 : ℚ) ^ (∑ i : ι, e i) :=
    Finset.prod_pow_eq_pow_sum Finset.univ e (2 : ℚ)
  calc
    (∏ i : ι, (3 + 1 / x i)) =
        (∏ i : ι, ((2 : ℚ) ^ e i * x (R i)) / x i) := by
      apply Finset.prod_congr rfl
      intro i _
      exact hfactor i
    _ = ((∏ i : ι, (2 : ℚ) ^ e i) * (∏ i : ι, x (R i))) /
        (∏ i : ι, x i) := by
      rw [Finset.prod_div_distrib, Finset.prod_mul_distrib]
    _ = (2 : ℚ) ^ (∑ i : ι, e i) := by
      rw [Equiv.prod_comp R x, hpow]
      exact mul_div_cancel_right₀ _ hprod_ne

/-- Positivity of the states makes every factor strictly greater than three.
Nonemptiness is explicit; the strict inequality is false for an empty index. -/
theorem cycle_factor_product_gt_three {ι : Type u} [Fintype ι]
    (x : ι → ℚ) (hx : ∀ i : ι, 0 < x i) (hι : Nonempty ι) :
    (3 : ℚ) ^ Fintype.card ι < (∏ i : ι, (3 + 1 / x i)) := by
  classical
  obtain ⟨i₀⟩ := hι
  have hfactor (i : ι) : (3 : ℚ) < 3 + 1 / x i := by
    have hrecip : (0 : ℚ) < 1 / x i := one_div_pos.mpr (hx i)
    linarith
  have hprod : (∏ _i : ι, (3 : ℚ)) <
      (∏ i : ι, (3 + 1 / x i)) :=
    Finset.prod_lt_prod
      (fun _ _ => by norm_num)
      (fun i _ => (hfactor i).le)
      ⟨i₀, Finset.mem_univ i₀, hfactor i₀⟩
  simpa only [Finset.prod_const, Finset.card_univ] using hprod

-- The following three proofs are the needed checked generic cycle-tools proofs.
private theorem iterate_positive (f : ℕ → ℕ)
    (hpos : ∀ n : ℕ, 0 < n → 0 < f n)
    (n : ℕ) (hn : 0 < n) (t : ℕ) : 0 < f^[t] n := by
  induction t with
  | zero => simpa using hn
  | succ t ih =>
      simpa only [Function.iterate_succ_apply'] using hpos (f^[t] n) ih

private theorem periodic_iterate {f : ℕ → ℕ} {m p : ℕ}
    (hcyc : f^[p] m = m) (t : ℕ) :
    f^[p] (f^[t] m) = f^[t] m := by
  calc
    f^[p] (f^[t] m) = f^[p + t] m := (Function.iterate_add_apply f p t m).symm
    _ = f^[t + p] m := by rw [Nat.add_comm]
    _ = f^[t] (f^[p] m) := Function.iterate_add_apply f t p m
    _ = f^[t] m := by rw [hcyc]

private theorem periodic_reaches_one {f : ℕ → ℕ} {m p t : ℕ}
    (hfix : f 1 = 1) (hp : 0 < p) (hcyc : f^[p] m = m)
    (hone : f^[t] m = 1) : m = 1 := by
  have hreturn : f^[p * t] m = m := by
    rw [Function.iterate_mul]
    exact Function.iterate_fixed hcyc t
  have ht : t ≤ p * t := by
    have h := Nat.mul_le_mul_right t (Nat.succ_le_of_lt hp)
    simpa using h
  have hreach : f^[p * t] m = 1 := by
    rw [show p * t = (p * t - t) + t by omega, Function.iterate_add_apply, hone]
    exact Function.iterate_fixed hfix (p * t - t)
  exact hreturn.symm.trans hreach

private theorem step_factorization (n : ℕ) :
    2 ^ ((3 * n + 1).factorization 2) * syracuseStep n = 3 * n + 1 := by
  exact Nat.ordProj_mul_ordCompl_eq_self (3 * n + 1) 2

-- No finite evaluator or trajectory band is needed for positivity.
private theorem syracuse_positive (n : ℕ) : 0 < syracuseStep n := by
  have hf := step_factorization n
  by_contra h
  have hz : syracuseStep n = 0 := by omega
  rw [hz, mul_zero] at hf
  omega

private theorem syracuse_one : syracuseStep 1 = 1 := by
  unfold syracuseStep
  have hf : 3 * (1 : ℕ) + 1 = 2 ^ 2 * 1 := by norm_num
  rw [hf]
  exact Nat.ordCompl_pow_mul_of_not_dvd 2 Nat.prime_two (by decide)

/-- The last-to-first edge uses the supplied return equality, not an
unproved periodicity or injectivity assumption. -/
private theorem syracuse_cycle_rotate (m p : ℕ) (hp : 0 < p)
    (hcycle : syracuseStep^[p] m = m) (i : Fin p) :
    syracuseStep^[(finRotate p i).val] m = syracuseStep (syracuseStep^[i.val] m) := by
  obtain ⟨q, hq⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hp)
  subst p
  rw [coe_finRotate]
  split_ifs with hi
  · rw [hi]
    simpa only [Fin.val_last, Function.iterate_zero_apply,
      Function.iterate_succ_apply'] using hcycle.symm
  · simp only [Function.iterate_succ_apply']

/-- Product identity on the actual Syracuse orbit, with a Fin p rotation
and the actual two-adic exponents. No minimal-period assumption is used. -/
theorem syracuse_cycle_factor_product (m p : ℕ) (hm : 0 < m) (hp : 0 < p)
    (hcycle : syracuseStep^[p] m = m) :
    (∏ i : Fin p, (3 + 1 / (syracuseStep^[i.val] m : ℚ))) =
      (2 : ℚ) ^ (∑ i : Fin p, (3 * syracuseStep^[i.val] m + 1).factorization 2) := by
  classical
  let x : Fin p → ℚ := fun i => (syracuseStep^[i.val] m : ℚ)
  let e : Fin p → ℕ := fun i => (3 * syracuseStep^[i.val] m + 1).factorization 2
  have hx : ∀ i : Fin p, 0 < x i := by
    intro i
    dsimp [x]
    exact_mod_cast
      iterate_positive syracuseStep (fun n _ => syracuse_positive n) m hm i.val
  have hedge : ∀ i : Fin p, (2 : ℚ) ^ e i * x (finRotate p i) = 3 * x i + 1 := by
    intro i
    have hn : 2 ^ ((3 * syracuseStep^[i.val] m + 1).factorization 2) *
        syracuseStep^[(finRotate p i).val] m = 3 * syracuseStep^[i.val] m + 1 := by
      rw [syracuse_cycle_rotate m p hp hcycle i]
      exact step_factorization (syracuseStep^[i.val] m)
    dsimp [x, e]
    exact_mod_cast hn
  simpa only [x, e] using cycle_factor_product (finRotate p) x e hx hedge

/-- A two-threshold criterion with genuinely independent supplied premises.

hsmall excludes periodic points below B ONLY.
hproduct bounds the entire factor product by (3 + 1/C)^p whenever the
finite cycle inputs are at least B; it does NOT posit input bounds at C.
hmargin is the arbitrary-K natural-number margin at C.

This theorem proves no instance of hproduct or hmargin. In particular it
is not a proof of fixed period 5626 or the unbounded mission tail. -/
theorem syracuse_two_threshold_criterion (p m B C : ℕ)
    (hp : 0 < p) (hm : 0 < m) (_hB : 0 < B) (hC : 0 < C)
    (hcycle : syracuseStep^[p] m = m)
    (hsmall : ∀ z a : ℕ, 0 < z → 0 < a → z < B →
      syracuseStep^[a] z = z → z = 1)
    (hproduct : (∀ i : Fin p, B ≤ syracuseStep^[i.val] m) →
      (∏ i : Fin p, (3 + 1 / (syracuseStep^[i.val] m : ℚ))) ≤
        (3 + 1 / (C : ℚ)) ^ p)
    (hmargin : ∀ K : ℕ, (3 : ℕ) ^ p < 2 ^ K →
      (3 * C + 1) ^ p < 2 ^ K * C ^ p) :
    m = 1 := by
  classical
  by_cases hvisit : ∃ t : ℕ, syracuseStep^[t] m < B
  · obtain ⟨t, ht⟩ := hvisit
    have hz : 0 < syracuseStep^[t] m :=
      iterate_positive syracuseStep (fun n _ => syracuse_positive n) m hm t
    have hperiod := periodic_iterate hcycle t
    have hone := hsmall (syracuseStep^[t] m) p hz hp ht hperiod
    exact periodic_reaches_one syracuse_one hp hcycle hone
  · have hmin : ∀ t : ℕ, B ≤ syracuseStep^[t] m := by
      intro t
      by_contra h
      exact hvisit ⟨t, by omega⟩
    have hx : ∀ i : Fin p, (0 : ℚ) < (syracuseStep^[i.val] m : ℚ) := by
      intro i
      exact_mod_cast
        iterate_positive syracuseStep (fun n _ => syracuse_positive n) m hm i.val
    let K : ℕ := ∑ i : Fin p, (3 * syracuseStep^[i.val] m + 1).factorization 2
    have hidentity :
        (∏ i : Fin p, (3 + 1 / (syracuseStep^[i.val] m : ℚ))) = (2 : ℚ) ^ K :=
      syracuse_cycle_factor_product m p hm hp hcycle
    have hstrict : (3 : ℚ) ^ p < (2 : ℚ) ^ K := by
      have hs := cycle_factor_product_gt_three
        (fun i : Fin p => (syracuseStep^[i.val] m : ℚ)) hx
        (show Nonempty (Fin p) from ⟨⟨0, hp⟩⟩)
      simpa only [Fintype.card_fin, hidentity] using hs
    have hthree : (3 : ℕ) ^ p < 2 ^ K := by
      exact_mod_cast hstrict
    have hupper := hproduct (fun i => hmin i.val)
    rw [hidentity] at hupper
    have hCq : (0 : ℚ) < (C : ℚ) := by exact_mod_cast hC
    have hCfactor : (3 + 1 / (C : ℚ)) * (C : ℚ) =
        ((3 * C + 1 : ℕ) : ℚ) := by
      push_cast
      field_simp [ne_of_gt hCq] <;> ring
    have hscaled : (2 : ℚ) ^ K * (C : ℚ) ^ p ≤
        ((3 * C + 1 : ℕ) : ℚ) ^ p := by
      calc
        (2 : ℚ) ^ K * (C : ℚ) ^ p ≤
            (3 + 1 / (C : ℚ)) ^ p * (C : ℚ) ^ p :=
          mul_le_mul_of_nonneg_right hupper (pow_nonneg hCq.le p)
        _ = ((3 * C + 1 : ℕ) : ℚ) ^ p := by
          rw [← mul_pow, hCfactor]
    have hupperNat : 2 ^ K * C ^ p ≤ (3 * C + 1) ^ p := by
      exact_mod_cast hscaled
    exact False.elim ((not_lt_of_ge hupperNat) (hmargin K hthree))

end CollatzTwoThresholdCriterionDraft01

/- Previously checked standalone arithmetic margin source. -/
namespace CollatzCycleMarginDraft5626

-- Kernel-checkable repeated squaring, with no finite-period table.
def binaryPow : Nat → Nat → Nat → Nat
  | _, _, 0 => 1
  | a, n, fuel + 1 =>
      let r := binaryPow a (n / 2) fuel
      if n % 2 = 0 then r * r else r * r * a

theorem binaryPow_eq (a n fuel : Nat) (h : n < 2 ^ fuel) :
    binaryPow a n fuel = a ^ n := by
  induction fuel generalizing n with
  | zero =>
      have hn : n = 0 := by simpa using h
      subst n
      rfl
  | succ fuel ih =>
      have hn : n / 2 < 2 ^ fuel := by
        rw [pow_succ] at h
        omega
      simp only [binaryPow, ih (n / 2) hn]
      split
      · rename_i heven
        have he : n = n / 2 + n / 2 := by omega
        rw [← pow_add, ← he]
      · rename_i hodd
        have he : n = n / 2 + n / 2 + 1 := by omega
        rw [← pow_add, ← pow_succ, ← he]

-- Only the isolated period 5626 at threshold B = 2786502 is certified.
theorem period_5626_certificate :
    binaryPow 2 8916 14 ≤ binaryPow 3 5626 14 ∧
      binaryPow (3 * 2786502 + 1) 5626 14 <
        binaryPow 2 8917 14 * binaryPow 2786502 5626 14 := by
  decide +kernel

theorem period_5626_bounds :
    (2 : Nat) ^ 8916 ≤ 3 ^ 5626 ∧
      (3 * 2786502 + 1 : Nat) ^ 5626 < 2 ^ 8917 * 2786502 ^ 5626 := by
  constructor
  · simpa only [binaryPow_eq 2 8916 14 (by decide),
      binaryPow_eq 3 5626 14 (by decide)] using period_5626_certificate.1
  · simpa only [binaryPow_eq (3 * 2786502 + 1) 5626 14 (by decide),
      binaryPow_eq 2 8917 14 (by decide),
      binaryPow_eq 2786502 5626 14 (by decide)] using period_5626_certificate.2

theorem margin_5626 (K : Nat) (h3 : (3 : Nat) ^ 5626 < 2 ^ K) :
    (3 * 2786502 + 1 : Nat) ^ 5626 < 2 ^ K * 2786502 ^ 5626 := by
  have hK : 8917 ≤ K := by
    by_cases h : 8917 ≤ K
    · exact h
    · have hle : K ≤ 8916 := Nat.le_of_lt_succ (Nat.lt_of_not_ge h)
      have hpow : (2 : Nat) ^ K ≤ 2 ^ 8916 :=
        Nat.pow_le_pow_right (by decide) hle
      exact False.elim ((Nat.not_lt_of_ge (hpow.trans period_5626_bounds.1)) h3)
  exact period_5626_bounds.2.trans_le (Nat.mul_le_mul_right (2786502 ^ 5626)
    (Nat.pow_le_pow_right (by decide) hK))

end CollatzCycleMarginDraft5626

namespace CollatzFixed5626Submission

/-- Cyclic four-window bounds work for every positive period, including periods
not divisible by four. The state threshold is B; the product threshold is C. -/
theorem cycle_product_upper (m p : ℕ) (hp : 0 < p)
    (hcycle : syracuseStep^[p] m = m)
    (hstates : ∀ i : Fin p, 2310000 ≤ syracuseStep^[i.val] m) :
    (∏ i : Fin p, (3 + 1 / (syracuseStep^[i.val] m : ℚ))) ≤
      (3 + 1 / (2786502 : ℚ)) ^ p := by
  classical
  let R : Equiv.Perm (Fin p) := finRotate p
  let x : Fin p → ℚ := fun i => (syracuseStep^[i.val] m : ℚ)
  let F : Fin p → ℚ := fun i => 3 + 1 / x i
  let L : ℚ := 3 + 1 / (2786502 : ℚ)
  have hxB (i : Fin p) : (2310000 : ℚ) ≤ x i := by
    dsimp [x]
    exact_mod_cast hstates i
  have hxpos (i : Fin p) : 0 < x i :=
    lt_of_lt_of_le (by norm_num : (0 : ℚ) < 2310000) (hxB i)
  have hF (i : Fin p) : 0 ≤ F i := by
    dsimp [F]
    exact (add_pos (by norm_num : (0 : ℚ) < 3) (one_div_pos.mpr (hxpos i))).le
  have hL : 0 ≤ L := by norm_num [L]
  have hedge (i : Fin p) :
      CollatzFourStateReciprocalDraft01.edge (x i) (x (R i)) := by
    have hperiod : syracuseStep^[p] (syracuseStep^[i.val] m) = syracuseStep^[i.val] m :=
      CollatzTwoThresholdCriterionDraft01.periodic_iterate hcycle i.val
    have hodd := CollatzSyracuseTransitionBridgeDraft01.periodic_point_odd
      (syracuseStep^[i.val] m) p hp hperiod
    dsimp [CollatzFourStateReciprocalDraft01.edge, x, R]
    rw [CollatzTwoThresholdCriterionDraft01.syracuse_cycle_rotate m p hp hcycle i]
    exact CollatzSyracuseTransitionBridgeDraft01.step_rational_edge _ hodd
  have hcap : (119 : ℚ) / (36 * (2310000 - 2)) ≤ 4 / (2786502 : ℚ) := by
    norm_num
  have hwindow (i : Fin p) :
      F i * F (R i) * F (R (R i)) * F (R (R (R i))) ≤ L ^ 4 := by
    have hrecip := CollatzFourStateReciprocalDraft01.four_state_reciprocal_bound
      (B := (2310000 : ℚ))
      (x0 := x i) (x1 := x (R i)) (x2 := x (R (R i))) (x3 := x (R (R (R i))))
      (by norm_num) (hxB i) (hxB (R i)) (hxB (R (R i))) (hxB (R (R (R i))))
      (hedge i) (hedge (R i)) (hedge (R (R i)))
    have hsum : F i + F (R i) + F (R (R i)) + F (R (R (R i))) ≤ 4 * L := by
      dsimp [F, L]
      linarith only [hrecip, hcap]
    exact CollatzFourWindowProductsDraft01.amgm4_bound
      (hF i) (hF (R i)) (hF (R (R i))) (hF (R (R (R i)))) hL hsum
  have hprod := CollatzFourWindowProductsDraft01.window_product_bound R F L hF hL hwindow
  simpa only [Fintype.card_fin, F, L, x] using hprod

end CollatzFixed5626Submission

theorem solution (m : ℕ) (hm : 0 < m)
    (hcyc : syracuseStep^[5626] m = m) :
    m = 1 := by
  exact CollatzTwoThresholdCriterionDraft01.syracuse_two_threshold_criterion
    5626 m 2310000 2786502 (by decide) hm (by decide) (by decide) hcyc
    (by
      intro z a hz ha hbound hreturn
      exact syracuse_no_cycle_below_2310000 z a hz ha (by omega) hreturn)
    (fun hstates =>
      CollatzFixed5626Submission.cycle_product_upper m 5626 (by decide) hcyc hstates)
    (fun K hthree => CollatzCycleMarginDraft5626.margin_5626 K hthree)

#print axioms solution
