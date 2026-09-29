-- Prove2me | solution 1 for rudelson_tangent_sampling_expected_deviation_core_bound_dense
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-06-23T03:56:13.684236+00:00
-- url     : https://prove2.me/submissions/9665dda0-da61-426d-b149-3109f012b12d

import Definitions.Def_matrix_completion_tangent
import Theorems.Thm_a0_implies_tangent_coordinate_frobenius_bound_min
import Theorems.Thm_rudelson_selection_expected_tangent_deviation_from_coordinate_radius_bound_dense_proviso
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.Monoid.Unbundled.MinMax

open MatrixCompletion
open scoped Classical BigOperators

/-! Reduction of `rudelson_tangent_sampling_expected_deviation_core_bound_dense` (84cb7b28)
    to the PROVISO radius node
    `rudelson_selection_expected_tangent_deviation_from_coordinate_radius_bound_dense_proviso`
    (66bc91bf) — the corrected leaf carrying the CR Thm 4.2 Part 1 desymmetrization proviso
    `√(log(max)/p)·R ≤ 1` — via the PROVED bridge
      - a0_implies_tangent_coordinate_frobenius_bound_min (2b86e79c): A0 ⟹ ‖P_T e_ij‖²≤2μ₀r/min.

    KEY: the proviso is SUPPLIED from the density hypothesis. With R=√(2μ₀r/min), A=log(max)/p,
    p=m/(n₁n₂)=m/(min·max):  (√A·R)² = A·R² = (log·min·max/m)·(2μ₀r/min) = 2μ₀·max·r·log/m.
    Density m ≥ β·μ₀·max·r·log(max), β>2 ⇒ 2μ₀·max·r·log/m ≤ 2/β < 1 ⇒ √A·R ≤ 1.

    Source: Candès–Recht 2009, arXiv:0805.4471, eq (4.8) p.18 (coordinate radius bound)
    + Thm 4.2 Part 1 eq (4.9) p.18 (radius-form selection estimate WITH the RHS≤1 proviso). -/
theorem solution :
    ∃ C : ℝ, 0 < C ∧
      ∀ (β : ℝ), 2 < β →
      ∀ (n₁ n₂ r m : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
        (μ₀ : ℝ) (S : SVD M r),
        0 < n₁ → 0 < n₂ → 0 < r → m ≤ n₁ * n₂ →
        1 ≤ μ₀ → A0 S μ₀ →
        (m : ℝ) ≥ β * μ₀ * (↑(max n₁ n₂)) * (r : ℝ) *
          Real.log (↑(max n₁ n₂)) →
        bernoulliExpectation ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega =>
              tangentSamplingDeviation Omega S
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) ≤
          tangentSamplingExpectedDeviationScale C μ₀ (max n₁ n₂) r m := by
  obtain ⟨Csel, hCsel, Hrad⟩ :=
    rudelson_selection_expected_tangent_deviation_from_coordinate_radius_bound_dense_proviso
  refine ⟨Csel * Real.sqrt 2, by positivity, ?_⟩
  intro β hβ n₁ n₂ r m M μ₀ S hn1 hn2 hr hm hμ₀ hA0 hdens
  have hcoord :=
    a0_implies_tangent_coordinate_frobenius_bound_min S μ₀ hn1 hn2 hr hμ₀ hA0
  have hμ₀nn : (0 : ℝ) ≤ μ₀ := le_trans zero_le_one hμ₀
  have hn1R : (0 : ℝ) < n₁ := by exact_mod_cast hn1
  have hn2R : (0 : ℝ) < n₂ := by exact_mod_cast hn2
  have hminN : 0 < min n₁ n₂ := by omega
  have hminR : (0 : ℝ) < (min n₁ n₂ : ℝ) := by exact_mod_cast hminN
  have hmaxN : 0 < max n₁ n₂ := lt_of_lt_of_le hn1 (le_max_left _ _)
  have hmaxR : (0 : ℝ) < (max n₁ n₂ : ℝ) := by exact_mod_cast hmaxN
  set Rbound : ℝ := 2 * μ₀ * (r : ℝ) / (min n₁ n₂ : ℝ) with hRb
  have hRbnn : 0 ≤ Rbound := by rw [hRb]; positivity
  set R : ℝ := Real.sqrt Rbound with hR
  have hRnn : 0 ≤ R := Real.sqrt_nonneg _
  have hpt : ∀ i : Fin n₁, ∀ j : Fin n₂,
      frobeniusNorm (tangentProjection S (coordinateMatrix i j)) ≤ R := by
    intro i j
    have hsq : frobeniusNorm (tangentProjection S (coordinateMatrix i j)) ^ 2 ≤ Rbound :=
      hcoord i j
    have hnn : 0 ≤ frobeniusNorm (tangentProjection S (coordinateMatrix i j)) :=
      Real.sqrt_nonneg _
    rw [hR, show frobeniusNorm (tangentProjection S (coordinateMatrix i j))
        = Real.sqrt (frobeniusNorm (tangentProjection S (coordinateMatrix i j)) ^ 2) from
      (Real.sqrt_sq hnn).symm]
    exact Real.sqrt_le_sqrt hsq
  have hlognn : 0 ≤ Real.log (↑(max n₁ n₂) : ℝ) := by
    apply Real.log_nonneg
    have : (1 : ℕ) ≤ max n₁ n₂ := hmaxN
    exact_mod_cast this
  have hrR : (0 : ℝ) ≤ r := by positivity
  have hβnn : 0 ≤ β := by linarith
  have hmaxRcast : (0 : ℝ) ≤ (↑(max n₁ n₂) : ℝ) := by positivity
  have hdens_rad : (m : ℝ) ≥ β * (↑(max n₁ n₂)) * (r : ℝ) *
      Real.log (↑(max n₁ n₂)) := by
    refine le_trans ?_ hdens
    have hbase : 0 ≤ β * (↑(max n₁ n₂) : ℝ) * (r : ℝ) * Real.log (↑(max n₁ n₂)) := by
      have := mul_nonneg (mul_nonneg (mul_nonneg hβnn hmaxRcast) hrR) hlognn
      simpa [mul_assoc] using this
    nlinarith [hbase, hμ₀, mul_nonneg (mul_nonneg (mul_nonneg hβnn hmaxRcast) hrR) hlognn]
  -- m = 0 is impossible under the density hyp once max≥1 and β>2... but handle uniformly:
  -- we need m>0 to talk about p; if m=0 the density forces 0 ≥ β·μ₀·max·r·log, and
  -- since RHS could be 0 (log=0 when max=1) we keep the general p>0 branch separate.
  rcases Nat.eq_zero_or_pos m with hm0 | hmpos
  · -- m = 0: then density says 0 ≥ β μ₀ max r log ≥ 0, so that product = 0.
    -- The deviation bound's LHS we bound by the proviso child applied with the trivial
    -- proviso (√0 · R = 0 ≤ 1 when log=0; when log>0 m=0 contradicts density).
    subst hm0
    -- density: 0 ≥ β μ₀ max r log(max). With β,μ₀≥1,max≥1,r>0 ⇒ log(max) ≤ 0 ⇒ log = 0.
    have hprodpos : 0 ≤ β * μ₀ * (↑(max n₁ n₂) : ℝ) * (r : ℝ) := by positivity
    have hlog0 : Real.log (↑(max n₁ n₂) : ℝ) = 0 := by
      by_contra hne
      have hlogpos : 0 < Real.log (↑(max n₁ n₂) : ℝ) := lt_of_le_of_ne hlognn (Ne.symm hne)
      have hpos : 0 < β * μ₀ * (↑(max n₁ n₂) : ℝ) * (r : ℝ) * Real.log (↑(max n₁ n₂)) := by
        have hβpos : 0 < β := by linarith
        have hrpos : (0:ℝ) < r := by exact_mod_cast hr
        positivity
      simp only [Nat.cast_zero] at hdens
      linarith [hdens, hpos]
    -- proviso holds trivially: √(log/p)·R with log=0 gives √0 = 0 ≤ 1
    have hprov : Real.sqrt (Real.log (↑(max n₁ n₂)) /
          (((0:ℕ) : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) * R ≤ 1 := by
      rw [hlog0]; simp
    have hExp := Hrad β hβ n₁ n₂ r 0 M S R hn1 hn2 hr hm hRnn hdens_rad hprov hpt
    refine le_trans hExp ?_
    -- RHS scale at m=0
    rw [hR, hRb]
    unfold tangentSamplingExpectedDeviationScale
    simp only [Nat.cast_max]
    have hL : Real.log (max (n₁:ℝ) (n₂:ℝ)) / (((0:ℕ) : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) = 0 := by
      simp
    have hLHS : Csel * Real.sqrt (Real.log (max (n₁:ℝ) (n₂:ℝ)) /
            ((((0:ℕ)) : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
          Real.sqrt (2 * μ₀ * (r : ℝ) / (min n₁ n₂ : ℝ)) = 0 := by
      rw [hL, Real.sqrt_zero, mul_zero, zero_mul]
    rw [hLHS]; positivity
  -- m > 0
  have hmR : (0 : ℝ) < m := by exact_mod_cast hmpos
  set p : ℝ := (m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)) with hp
  have hppos : 0 < p := by rw [hp]; positivity
  -- supply the proviso: √(log/p)·R ≤ 1.  Square it: A·R² = A·B = 2μ₀ max r log / m ≤ 2/β < 1.
  set A : ℝ := Real.log (↑(max n₁ n₂) : ℝ) / p with hAdef
  have hApos : 0 ≤ A := by rw [hAdef]; exact div_nonneg hlognn hppos.le
  have hprov : Real.sqrt (Real.log (↑(max n₁ n₂)) / p) * R ≤ 1 := by
    have hmerge : Real.sqrt A * R = Real.sqrt (A * Rbound) := by
      rw [hR, ← Real.sqrt_mul hApos]
    have hkey : A * Rbound ≤ 1 := by
      -- A * Rbound = (log/p) * (2μ₀r/min) = 2μ₀·max·r·log/m  (since p = m/(min·max))
      have hprodeq : (n₁ : ℝ) * (n₂ : ℝ) = (min n₁ n₂ : ℝ) * (max n₁ n₂ : ℝ) := by
        have := congrArg (Nat.cast : ℕ → ℝ) ((min_mul_max n₁ n₂).symm)
        push_cast at this; exact this
      have hmne : (m:ℝ) ≠ 0 := ne_of_gt hmR
      have hminne : (min n₁ n₂ : ℝ) ≠ 0 := ne_of_gt hminR
      have hmaxne : (max n₁ n₂ : ℝ) ≠ 0 := ne_of_gt hmaxR
      have hval : A * Rbound
          = 2 * μ₀ * (↑(max n₁ n₂):ℝ) * (r:ℝ) * Real.log (↑(max n₁ n₂)) / (m:ℝ) := by
        rw [hAdef, hRb, hp, hprodeq]
        push_cast
        field_simp
      rw [hval]
      -- now show 2μ₀·max·r·log/m ≤ 1, i.e. 2μ₀·max·r·log ≤ m, from density (β>2)
      rw [div_le_one hmR]
      have h2β : (2:ℝ) ≤ β := by linarith
      have hb : 0 ≤ μ₀ * (↑(max n₁ n₂):ℝ) * (r:ℝ) * Real.log (↑(max n₁ n₂)) := by positivity
      nlinarith [hdens, hb, h2β, mul_nonneg hb (by linarith : (0:ℝ) ≤ β - 2)]
    calc Real.sqrt (Real.log (↑(max n₁ n₂)) / p) * R
        = Real.sqrt (A * Rbound) := by rw [hAdef] at hmerge ⊢; exact hmerge
      _ ≤ Real.sqrt 1 := Real.sqrt_le_sqrt hkey
      _ = 1 := Real.sqrt_one
  have hExp := Hrad β hβ n₁ n₂ r m M S R hn1 hn2 hr hm hRnn hdens_rad hprov hpt
  refine le_trans hExp ?_
  rw [hR, hRb]
  unfold tangentSamplingExpectedDeviationScale
  simp only [Nat.cast_max]
  have hmax1 : (1 : ℝ) ≤ (max n₁ n₂ : ℝ) := by
    have : 1 ≤ max n₁ n₂ := hmaxN
    exact_mod_cast this
  have hlognn' : 0 ≤ Real.log (max (n₁:ℝ) (n₂:ℝ)) := Real.log_nonneg hmax1
  set A' : ℝ := Real.log (max (n₁:ℝ) (n₂:ℝ)) / p with hA'
  set B : ℝ := 2 * μ₀ * (r : ℝ) / (min n₁ n₂ : ℝ) with hB
  have hA'pos : 0 ≤ A' := by rw [hA']; exact div_nonneg hlognn' hppos.le
  have hBpos : 0 ≤ B := by rw [hB]; positivity
  have hmerge : Real.sqrt A' * Real.sqrt B = Real.sqrt (A' * B) :=
    (Real.sqrt_mul hA'pos B).symm
  rw [mul_assoc, hmerge]
  set D : ℝ := μ₀ * (max (n₁:ℝ) (n₂:ℝ)) * (r : ℝ) * Real.log (max (n₁:ℝ) (n₂:ℝ)) / (m : ℝ) with hD
  have hDpos : 0 ≤ D := by rw [hD]; apply div_nonneg _ hmR.le; positivity
  rw [mul_assoc, show Real.sqrt 2 * Real.sqrt D = Real.sqrt (2 * D) from
    (Real.sqrt_mul (by norm_num) D).symm]
  apply mul_le_mul_of_nonneg_left _ hCsel.le
  apply Real.sqrt_le_sqrt
  rw [hA', hB, hD, hp]
  rw [div_div_eq_mul_div, div_mul_div_comm]
  rw [mul_div_assoc']
  rw [div_le_div_iff₀ (by positivity) hmR]
  have hprodeqN : n₁ * n₂ = min n₁ n₂ * max n₁ n₂ := (min_mul_max n₁ n₂).symm
  have hprodeq : (n₁ : ℝ) * (n₂ : ℝ) = (min n₁ n₂ : ℝ) * (max n₁ n₂ : ℝ) := by
    have := congrArg (Nat.cast : ℕ → ℝ) hprodeqN
    push_cast at this; exact this
  rw [hprodeq]
  apply le_of_eq
  ring
