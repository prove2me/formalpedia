-- Prove2me | solution 1 for mme_modern_entropyBits_additive_certificate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-25T08:37:39.92926+00:00
-- url     : https://prove2.me/submissions/8d4b84e6-4555-4163-ba14-94b6fffa6d76

import Definitions.Def_mme_modern_entropy_data
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

open BigOperators

universe u v w x

private theorem negMulLog_le_tangent {r y : ℝ} (hr : 0 ≤ r) (hy : 0 < y) :
    Real.negMulLog r ≤
      Real.negMulLog y + (-Real.log y - 1) * (r - y) := by
  rcases hr.eq_or_lt with rfl | hr
  · rw [Real.negMulLog_zero, Real.negMulLog]
    nlinarith
  · have hratio : 0 < y / r := div_pos hy hr
    have hlog := Real.log_le_sub_one_of_pos hratio
    have hmul := mul_le_mul_of_nonneg_left hlog hr.le
    rw [Real.log_div hy.ne' hr.ne'] at hmul
    rw [Real.negMulLog, Real.negMulLog]
    field_simp at hmul
    nlinarith

private theorem entropyNat_le_tangent
    {D : Type u} [Fintype D] (r y : D → ℝ)
    (hr : ∀ a, 0 ≤ r a) (hy : ∀ a, 0 < y a) :
    (∑ a, Real.negMulLog (r a)) ≤
      (∑ a, Real.negMulLog (y a)) +
        ∑ a, (-Real.log (y a) - 1) * (r a - y a) := by
  calc
    (∑ a, Real.negMulLog (r a)) ≤
        ∑ a, (Real.negMulLog (y a) +
          (-Real.log (y a) - 1) * (r a - y a)) := by
            exact Finset.sum_le_sum fun a _ha => negMulLog_le_tangent (hr a) (hy a)
    _ = (∑ a, Real.negMulLog (y a)) +
        ∑ a, (-Real.log (y a) - 1) * (r a - y a) := by
          rw [Finset.sum_add_distrib]

private theorem sum_abs_sub_le_two
    {D : Type u} [Fintype D] (p r : D → ℝ)
    (hp : ∀ a, 0 ≤ p a) (hr : ∀ a, 0 ≤ r a)
    (hpsum : ∑ a, p a = 1) (hrsum : ∑ a, r a = 1) :
    ∑ a, |p a - r a| ≤ 2 := by
  calc
    (∑ a, |p a - r a|) ≤ ∑ a, (p a + r a) := by
      apply Finset.sum_le_sum
      intro a _ha
      simpa [abs_of_nonneg (hp a), abs_of_nonneg (hr a)] using
        (abs_sub_le (p a) 0 (r a))
    _ = (∑ a, p a) + ∑ a, r a := by rw [Finset.sum_add_distrib]
    _ = 2 := by rw [hpsum, hrsum]; norm_num

private theorem sum_potential_mul_sub_eq_zero
    {D : Type u} {I : Type v} [Fintype D] [Fintype I] [DecidableEq I]
    (coord : D → I) (p r : D → ℝ) (potential : I → ℝ)
    (hmarg : ∀ i, mme_modern_marginal coord p i =
      mme_modern_marginal coord r i) :
    ∑ a, potential (coord a) * (p a - r a) = 0 := by
  rw [← Fintype.sum_fiberwise coord
    (fun a => potential (coord a) * (p a - r a))]
  apply Finset.sum_eq_zero
  intro i _hi
  calc
    (∑ a : {a // coord a = i},
        potential (coord a) * (p a - r a)) =
        potential i *
          (mme_modern_marginal coord p i - mme_modern_marginal coord r i) := by
          simp_rw [show ∀ a : {a // coord a = i}, coord a = i from fun a => a.property]
          rw [← Finset.mul_sum, Finset.sum_sub_distrib]
          rfl
    _ = 0 := by rw [hmarg i, sub_self, mul_zero]

private theorem sum_additive_potential_mul_sub_eq_zero
    {D : Type u} {X : Type v} {Y : Type w} {Z : Type x}
    [Fintype D] [Fintype X] [Fintype Y] [Fintype Z]
    [DecidableEq X] [DecidableEq Y] [DecidableEq Z]
    (coordX : D → X) (coordY : D → Y) (coordZ : D → Z)
    (p r : D → ℝ) (c : ℝ)
    (potentialX : X → ℝ) (potentialY : Y → ℝ) (potentialZ : Z → ℝ)
    (hmass : ∑ a, p a = ∑ a, r a)
    (hmargX : ∀ i, mme_modern_marginal coordX p i =
      mme_modern_marginal coordX r i)
    (hmargY : ∀ i, mme_modern_marginal coordY p i =
      mme_modern_marginal coordY r i)
    (hmargZ : ∀ i, mme_modern_marginal coordZ p i =
      mme_modern_marginal coordZ r i) :
    ∑ a, (c + potentialX (coordX a) + potentialY (coordY a) +
      potentialZ (coordZ a)) * (p a - r a) = 0 := by
  have hc : ∑ a, c * (p a - r a) = 0 := by
    rw [← Finset.mul_sum, Finset.sum_sub_distrib, hmass, sub_self, mul_zero]
  have hx := sum_potential_mul_sub_eq_zero coordX p r potentialX hmargX
  have hy := sum_potential_mul_sub_eq_zero coordY p r potentialY hmargY
  have hz := sum_potential_mul_sub_eq_zero coordZ p r potentialZ hmargZ
  simp_rw [add_mul]
  repeat' rw [Finset.sum_add_distrib]
  rw [hc, hx, hy, hz]
  norm_num

private theorem entropyNat_additive_certificate
    {D : Type u} {X : Type v} {Y : Type w} {Z : Type x}
    [Fintype D] [Fintype X] [Fintype Y] [Fintype Z]
    [DecidableEq X] [DecidableEq Y] [DecidableEq Z]
    (coordX : D → X) (coordY : D → Y) (coordZ : D → Z)
    (rho y : D → ℝ)
    (lambdaZero : ℝ)
    (lambdaX : X → ℝ) (lambdaY : Y → ℝ) (lambdaZ : Z → ℝ)
    (ε : ℝ)
    (hrho : ∀ a, 0 ≤ rho a) (hy : ∀ a, 0 < y a)
    (hrhoSum : ∑ a, rho a = 1) (hySum : ∑ a, y a = 1)
    (hmargX : ∀ i, mme_modern_marginal coordX rho i =
      mme_modern_marginal coordX y i)
    (hmargY : ∀ i, mme_modern_marginal coordY rho i =
      mme_modern_marginal coordY y i)
    (hmargZ : ∀ i, mme_modern_marginal coordZ rho i =
      mme_modern_marginal coordZ y i)
    (hε : 0 ≤ ε)
    (hcertificate : ∀ a,
      |Real.log (y a) -
        (lambdaZero + lambdaX (coordX a) + lambdaY (coordY a) +
          lambdaZ (coordZ a))| ≤ ε) :
    (∑ a, Real.negMulLog (rho a)) ≤
      (∑ a, Real.negMulLog (y a)) + 2 * ε := by
  let g : D → ℝ := fun a =>
    lambdaZero + lambdaX (coordX a) + lambdaY (coordY a) + lambdaZ (coordZ a)
  have hmass : ∑ a, rho a = ∑ a, y a := by rw [hrhoSum, hySum]
  have hcancel :
      ∑ a, ((lambdaZero + 1) + lambdaX (coordX a) + lambdaY (coordY a) +
        lambdaZ (coordZ a)) * (rho a - y a) = 0 :=
    sum_additive_potential_mul_sub_eq_zero coordX coordY coordZ rho y
      (lambdaZero + 1) lambdaX lambdaY lambdaZ hmass hmargX hmargY hmargZ
  have hreframe :
      ∑ a, (-Real.log (y a) - 1) * (rho a - y a) =
        ∑ a, (g a - Real.log (y a)) * (rho a - y a) := by
    calc
      (∑ a, (-Real.log (y a) - 1) * (rho a - y a)) =
          ∑ a, ((g a - Real.log (y a)) -
            ((lambdaZero + 1) + lambdaX (coordX a) + lambdaY (coordY a) +
              lambdaZ (coordZ a))) * (rho a - y a) := by
                apply Finset.sum_congr rfl
                intro a _ha
                dsimp [g]
                ring
      _ = (∑ a, (g a - Real.log (y a)) * (rho a - y a)) -
          ∑ a, ((lambdaZero + 1) + lambdaX (coordX a) + lambdaY (coordY a) +
            lambdaZ (coordZ a)) * (rho a - y a) := by
              simp_rw [sub_mul]
              rw [Finset.sum_sub_distrib]
      _ = ∑ a, (g a - Real.log (y a)) * (rho a - y a) := by
            rw [hcancel, sub_zero]
  have hl1 : ∑ a, |rho a - y a| ≤ 2 :=
    sum_abs_sub_le_two rho y hrho (fun a => (hy a).le) hrhoSum hySum
  have hresidual :
      ∑ a, (g a - Real.log (y a)) * (rho a - y a) ≤ 2 * ε := by
    calc
      (∑ a, (g a - Real.log (y a)) * (rho a - y a)) ≤
          ∑ a, ε * |rho a - y a| := by
            apply Finset.sum_le_sum
            intro a _ha
            calc
              (g a - Real.log (y a)) * (rho a - y a) ≤
                  |(g a - Real.log (y a)) * (rho a - y a)| :=
                le_abs_self _
              _ = |g a - Real.log (y a)| * |rho a - y a| := abs_mul _ _
              _ ≤ ε * |rho a - y a| := by
                apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
                simpa only [g, abs_sub_comm] using hcertificate a
      _ = ε * ∑ a, |rho a - y a| := by rw [Finset.mul_sum]
      _ ≤ ε * 2 := mul_le_mul_of_nonneg_left hl1 hε
      _ = 2 * ε := by ring
  calc
    (∑ a, Real.negMulLog (rho a)) ≤
        (∑ a, Real.negMulLog (y a)) +
          ∑ a, (-Real.log (y a) - 1) * (rho a - y a) :=
      entropyNat_le_tangent rho y hrho hy
    _ = (∑ a, Real.negMulLog (y a)) +
        ∑ a, (g a - Real.log (y a)) * (rho a - y a) := by rw [hreframe]
    _ ≤ (∑ a, Real.negMulLog (y a)) + 2 * ε := by gcongr

theorem solution
    {D : Type u} {X : Type v} {Y : Type w} {Z : Type x}
    [Fintype D] [Fintype X] [Fintype Y] [Fintype Z]
    [DecidableEq X] [DecidableEq Y] [DecidableEq Z]
    (coordX : D → X) (coordY : D → Y) (coordZ : D → Z)
    (rho y : D → ℝ)
    (lambdaZero : ℝ)
    (lambdaX : X → ℝ) (lambdaY : Y → ℝ) (lambdaZ : Z → ℝ)
    (ε : ℝ)
    (hrho : ∀ a, 0 ≤ rho a) (hy : ∀ a, 0 < y a)
    (hrhoSum : ∑ a, rho a = 1) (hySum : ∑ a, y a = 1)
    (hmargX : ∀ i, mme_modern_marginal coordX rho i =
      mme_modern_marginal coordX y i)
    (hmargY : ∀ i, mme_modern_marginal coordY rho i =
      mme_modern_marginal coordY y i)
    (hmargZ : ∀ i, mme_modern_marginal coordZ rho i =
      mme_modern_marginal coordZ y i)
    (hε : 0 ≤ ε)
    (hcertificate : ∀ a,
      |Real.log (y a) / Real.log 2 -
        (lambdaZero + lambdaX (coordX a) + lambdaY (coordY a) +
          lambdaZ (coordZ a))| ≤ ε) :
    mme_modern_entropyBits rho ≤ mme_modern_entropyBits y + 2 * ε := by
  have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hcertificateNat : ∀ a,
      |Real.log (y a) -
        ((Real.log 2 * lambdaZero) +
          (Real.log 2 * lambdaX (coordX a)) +
          (Real.log 2 * lambdaY (coordY a)) +
          (Real.log 2 * lambdaZ (coordZ a)))| ≤ Real.log 2 * ε := by
    intro a
    have halgebra :
        Real.log (y a) -
          ((Real.log 2 * lambdaZero) +
            (Real.log 2 * lambdaX (coordX a)) +
            (Real.log 2 * lambdaY (coordY a)) +
            (Real.log 2 * lambdaZ (coordZ a))) =
          Real.log 2 *
            (Real.log (y a) / Real.log 2 -
              (lambdaZero + lambdaX (coordX a) + lambdaY (coordY a) +
                lambdaZ (coordZ a))) := by
      field_simp
    rw [halgebra, abs_mul, abs_of_pos hlogTwo]
    exact mul_le_mul_of_nonneg_left (hcertificate a) hlogTwo.le
  have hnat := entropyNat_additive_certificate
    coordX coordY coordZ rho y
    (Real.log 2 * lambdaZero)
    (fun i => Real.log 2 * lambdaX i)
    (fun i => Real.log 2 * lambdaY i)
    (fun i => Real.log 2 * lambdaZ i)
    (Real.log 2 * ε)
    hrho hy hrhoSum hySum hmargX hmargY hmargZ
    (mul_nonneg hlogTwo.le hε) hcertificateNat
  unfold mme_modern_entropyBits
  calc
    (∑ a, Real.negMulLog (rho a)) / Real.log 2 ≤
        ((∑ a, Real.negMulLog (y a)) + 2 * (Real.log 2 * ε)) /
          Real.log 2 :=
      (div_le_div_iff_of_pos_right hlogTwo).2 hnat
    _ = (∑ a, Real.negMulLog (y a)) / Real.log 2 + 2 * ε := by
      field_simp
