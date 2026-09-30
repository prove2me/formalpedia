-- Prove2me | solution 1 for linear_neumann_diagonal_centered_contribution_small_with_lambda
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-06T04:20:17.716397+00:00
-- url     : https://prove2.me/submissions/86e341fe-02b8-46af-9597-c61d57116e2c

import Definitions.Def_matrix_completion_neumann
import Theorems.Thm_fixed_matrix_centered_sampling_spectral_bound
import Theorems.Thm_linear_neumann_diagonal_centered_as_fixed_matrix_fluctuation
import Theorems.Thm_linear_neumann_lambda_sample_lower_implies_fixed_matrix_sample_lower
open MatrixCompletion

open scoped Classical

/-- Parseval identity for an orthonormal family given in coordinates. -/
lemma mcParseval {r N : ℕ} (w : Fin r → Fin N → ℝ)
    (hw : ∀ k l, ∑ i, w k i * w l i = if k = l then 1 else 0) (c : Fin r → ℝ) :
    ∑ j, (∑ k, c k * w k j) ^ 2 = ∑ k, c k ^ 2 := by
  have h1 : ∀ j, (∑ k, c k * w k j) ^ 2 = ∑ k, ∑ l, (c k * c l) * (w k j * w l j) := by
    intro j
    rw [sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring
  simp_rw [h1]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, hw]
  simp [sq]

lemma mcSignEntry {n1 n2 r : ℕ} {M : RealMatrix n1 n2} (S : SVD M r) (a : Fin n1) (b : Fin n2) :
    signMatrix S a b = ∑ k, S.u k a * S.v k b := by
  unfold signMatrix
  simp [Matrix.sum_apply, Matrix.vecMulVec_apply]

lemma mcInnerCoord {n1 n2 : ℕ} (X : RealMatrix n1 n2) (a : Fin n1) (b : Fin n2) :
    matrixInner X (coordinateMatrix a b) = X a b := by
  unfold matrixInner coordinateMatrix
  simp [ite_and, Finset.sum_ite_eq']

lemma mcLeft {n1 n2 r : ℕ} {M : RealMatrix n1 n2} (S : SVD M r) (a : Fin n1) (b : Fin n2) :
    leftSingularProjection S (coordinateMatrix a b) a b = ∑ k, S.u k a ^ 2 := by
  unfold leftSingularProjection coordinateMatrix
  simp [ite_and, Finset.sum_ite_eq', sq]

lemma mcRight {n1 n2 r : ℕ} {M : RealMatrix n1 n2} (S : SVD M r) (a : Fin n1) (b : Fin n2) :
    rightSingularProjection S (coordinateMatrix a b) a b = ∑ k, S.v k b ^ 2 := by
  unfold rightSingularProjection coordinateMatrix
  simp [ite_and, Finset.sum_ite_eq', sq]

lemma mcTwo {n1 n2 r : ℕ} {M : RealMatrix n1 n2} (S : SVD M r) (a : Fin n1) (b : Fin n2) :
    twoSidedSingularProjection S (coordinateMatrix a b) a b =
      (∑ k, S.u k a ^ 2) * (∑ k, S.v k b ^ 2) := by
  unfold twoSidedSingularProjection coordinateMatrix
  simp [ite_and, Finset.sum_ite_eq', sq]

/-- The diagonal tangent kernel in closed form. -/
lemma mcKernel {n1 n2 r : ℕ} {M : RealMatrix n1 n2} (S : SVD M r) (a : Fin n1) (b : Fin n2) :
    tangentCoordinateKernel S a b a b =
      (∑ k, S.u k a ^ 2) + (∑ k, S.v k b ^ 2) - (∑ k, S.u k a ^ 2) * (∑ k, S.v k b ^ 2) := by
  unfold tangentCoordinateKernel
  rw [mcInnerCoord]
  unfold tangentProjection
  rw [Matrix.sub_apply, Matrix.add_apply, mcLeft, mcRight, mcTwo]

lemma mcSpectralSmul {n1 n2 : ℕ} (c : ℝ) (X : RealMatrix n1 n2) :
    spectralNorm (c • X) = |c| * spectralNorm X := by
  unfold spectralNorm
  rw [map_smul, map_smul, norm_smul, Real.norm_eq_abs]

lemma mcSpectralNonneg {n1 n2 : ℕ} (X : RealMatrix n1 n2) : 0 ≤ spectralNorm X := by
  unfold spectralNorm; exact norm_nonneg _

lemma mcEventMono {n1 n2 : ℕ} (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (E₁ E₂ : Finset (Fin n1 × Fin n2) → Prop) (h : ∀ Ω, E₁ Ω → E₂ Ω) :
    bernoulliEventProb p E₁ ≤ bernoulliEventProb p E₂ := by
  unfold bernoulliEventProb
  refine Finset.sum_le_sum fun Ω _ => ?_
  have hw : 0 ≤ bernoulliObservationWeight p Ω := by
    unfold bernoulliObservationWeight
    have : 0 ≤ 1 - p := by linarith
    positivity
  by_cases h1 : E₁ Ω
  · rw [if_pos h1, if_pos (h Ω h1)]
  · rw [if_neg h1]
    split_ifs <;> simp [hw]

lemma mcEventNonneg {n1 n2 : ℕ} (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (E : Finset (Fin n1 × Fin n2) → Prop) :
    0 ≤ bernoulliEventProb p E := by
  unfold bernoulliEventProb
  refine Finset.sum_nonneg fun Ω _ => ?_
  have hw : 0 ≤ bernoulliObservationWeight p Ω := by
    unfold bernoulliObservationWeight
    have : 0 ≤ 1 - p := by linarith
    positivity
  split_ifs <;> simp [hw]

lemma mcBase {n1 n2 r : ℕ} {M : RealMatrix n1 n2} (S : SVD M r) (a : Fin n1) (b : Fin n2) :
    linearNeumannDiagonalBaseMatrix S a b =
      signMatrix S a b * tangentCoordinateKernel S a b a b := rfl

/-- Entry sup-norm bound for the fixed diagonal matrix `H_ab = E_ab ⟪P_T e_ab, e_ab⟫`,
using only the incoherence assumption A1. -/
lemma mcSupBound {n₁ n₂ r : ℕ} {M : RealMatrix n₁ n₂} (S : SVD M r) (μ₁ : ℝ) (hμ₁ : 0 ≤ μ₁)
    (hn₁ : 0 < n₁) (hn₂ : 0 < n₂) (hA1 : A1 S μ₁) (n : ℕ) (hn1 : n₁ ≤ n) (hn2 : n₂ ≤ n) :
    entrySupNorm (linearNeumannDiagonalBaseMatrix S) ≤
      μ₁ * Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
        (μ₁ ^ 2 * (r : ℝ) * (2 * (n : ℝ)) / ((n₁ : ℝ) * (n₂ : ℝ))) := by
  have : Nonempty (Fin n₁) := ⟨⟨0, hn₁⟩⟩
  have : Nonempty (Fin n₂) := ⟨⟨0, hn₂⟩⟩
  have hn₁' : (0 : ℝ) < n₁ := by exact_mod_cast hn₁
  have hn₂' : (0 : ℝ) < n₂ := by exact_mod_cast hn₂
  have hNpos : (0 : ℝ) < (n₁ : ℝ) * (n₂ : ℝ) := by positivity
  unfold entrySupNorm
  refine ciSup_le fun a => ciSup_le fun b => ?_
  have hE : ∀ i j, |signMatrix S i j| ≤ μ₁ * Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) := hA1
  have hE2 : ∀ i j, signMatrix S i j ^ 2 ≤ μ₁ ^ 2 * ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) := by
    intro i j
    calc signMatrix S i j ^ 2 = |signMatrix S i j| ^ 2 := (sq_abs _).symm
      _ ≤ (μ₁ * Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) ^ 2 :=
          pow_le_pow_left₀ (abs_nonneg _) (hE i j) 2
      _ = μ₁ ^ 2 * ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) := by
          rw [mul_pow, Real.sq_sqrt (by positivity)]
  have hα0 : 0 ≤ ∑ k, S.u k a ^ 2 := Finset.sum_nonneg fun k _ => sq_nonneg _
  have hγ0 : 0 ≤ ∑ k, S.v k b ^ 2 := Finset.sum_nonneg fun k _ => sq_nonneg _
  have hαP : ∑ j, signMatrix S a j ^ 2 = ∑ k, S.u k a ^ 2 := by
    simp_rw [mcSignEntry]
    exact mcParseval S.v S.v_orthonormal (fun k => S.u k a)
  have hγP : ∑ i, signMatrix S i b ^ 2 = ∑ k, S.v k b ^ 2 := by
    simp_rw [mcSignEntry]
    have : ∀ i, (∑ k, S.u k i * S.v k b) = ∑ k, S.v k b * S.u k i :=
      fun i => Finset.sum_congr rfl fun k _ => mul_comm _ _
    simp_rw [this]
    exact mcParseval S.u S.u_orthonormal (fun k => S.v k b)
  have hα : ∑ k, S.u k a ^ 2 ≤ μ₁ ^ 2 * r / n₁ := by
    rw [← hαP]
    calc ∑ j, signMatrix S a j ^ 2
        ≤ ∑ j : Fin n₂, μ₁ ^ 2 * ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) :=
          Finset.sum_le_sum fun j _ => hE2 a j
      _ = (n₂ : ℝ) * (μ₁ ^ 2 * ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) := by simp
      _ = μ₁ ^ 2 * r / n₁ := by field_simp
  have hγ : ∑ k, S.v k b ^ 2 ≤ μ₁ ^ 2 * r / n₂ := by
    rw [← hγP]
    calc ∑ i, signMatrix S i b ^ 2
        ≤ ∑ i : Fin n₁, μ₁ ^ 2 * ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) :=
          Finset.sum_le_sum fun i _ => hE2 i b
      _ = (n₁ : ℝ) * (μ₁ ^ 2 * ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) := by simp
      _ = μ₁ ^ 2 * r / n₂ := by field_simp
  have hγ1 : ∑ k, S.v k b ^ 2 ≤ 1 := by
    have hPar : ∑ j, (∑ k, S.v k b * S.v k j) ^ 2 = ∑ k, S.v k b ^ 2 :=
      mcParseval S.v S.v_orthonormal (fun k => S.v k b)
    have hsingle : (∑ k, S.v k b * S.v k b) ^ 2 ≤ ∑ j, (∑ k, S.v k b * S.v k j) ^ 2 :=
      Finset.single_le_sum (f := fun j => (∑ k, S.v k b * S.v k j) ^ 2)
        (fun j _ => sq_nonneg _) (Finset.mem_univ b)
    have hdiag : (∑ k, S.v k b * S.v k b) = ∑ k, S.v k b ^ 2 := by simp [sq]
    rw [hdiag, hPar] at hsingle
    nlinarith
  have hK : tangentCoordinateKernel S a b a b =
      (∑ k, S.u k a ^ 2) + (∑ k, S.v k b ^ 2) - (∑ k, S.u k a ^ 2) * (∑ k, S.v k b ^ 2) :=
    mcKernel S a b
  have hK0 : 0 ≤ tangentCoordinateKernel S a b a b := by rw [hK]; nlinarith
  have hKle : tangentCoordinateKernel S a b a b ≤ (∑ k, S.u k a ^ 2) + (∑ k, S.v k b ^ 2) := by
    rw [hK]; nlinarith
  have hsum : μ₁ ^ 2 * r / n₁ + μ₁ ^ 2 * r / n₂ ≤
      μ₁ ^ 2 * (r : ℝ) * (2 * (n : ℝ)) / ((n₁ : ℝ) * (n₂ : ℝ)) := by
    have h1 : (n₁ : ℝ) ≤ n := by exact_mod_cast hn1
    have h2 : (n₂ : ℝ) ≤ n := by exact_mod_cast hn2
    have heq : μ₁ ^ 2 * r / n₁ + μ₁ ^ 2 * r / n₂ =
        μ₁ ^ 2 * (r : ℝ) * ((n₁ : ℝ) + n₂) / ((n₁ : ℝ) * (n₂ : ℝ)) := by
      field_simp; ring
    rw [heq]
    gcongr
    linarith
  rw [mcBase, abs_mul, abs_of_nonneg hK0]
  calc |signMatrix S a b| * tangentCoordinateKernel S a b a b
      ≤ (μ₁ * Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
          ((∑ k, S.u k a ^ 2) + (∑ k, S.v k b ^ 2)) :=
        mul_le_mul (hE a b) hKle hK0 (by positivity)
    _ ≤ (μ₁ * Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
          (μ₁ ^ 2 * r / n₁ + μ₁ ^ 2 * r / n₂) := by gcongr
    _ ≤ μ₁ * Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
          (μ₁ ^ 2 * (r : ℝ) * (2 * (n : ℝ)) / ((n₁ : ℝ) * (n₂ : ℝ))) := by gcongr

theorem solution :
    ∃ Ccenter ccenter : ℝ, 0 < Ccenter ∧ 0 < ccenter ∧
      ∀ (β lam : ℝ), 2 < β → 1 ≤ lam →
      ∀ (n₁ n₂ r m : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
        (μ₀ μ₁ : ℝ) (S : SVD M r),
        0 < n₁ → 0 < n₂ → 0 < r → m ≤ n₁ * n₂ →
        1 ≤ μ₀ → 1 ≤ μ₁ →
        A0 S μ₀ → A1 S μ₁ →
        (m : ℝ) ≥
          lam * μ₁ * max (Real.sqrt μ₀) μ₁ *
            (↑(max n₁ n₂)) * (r : ℝ) *
              (β * Real.log (↑(max n₁ n₂))) →
        bernoulliEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega =>
              spectralNorm
                (linearNeumannDiagonalCenteredContribution Omega S
                  ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) ≤
                Ccenter * Real.rpow lam (-1)) ≥
          1 - ccenter * Real.rpow (↑(max n₁ n₂)) (-β) := by
  obtain ⟨Cf, hCf, hfixed⟩ := fixed_matrix_centered_sampling_spectral_bound
  refine ⟨2 * Cf, 1, by positivity, one_pos, ?_⟩
  intro β lam hβ hlam n₁ n₂ r m M μ₀ μ₁ S hn₁ hn₂ hr hm hμ₀ hμ₁ _hA0 hA1 hmlow
  have hmQ := linear_neumann_lambda_sample_lower_implies_fixed_matrix_sample_lower
    β lam n₁ n₂ r m μ₀ μ₁ hβ hlam hn₁ hn₂ hr hμ₀ hμ₁ hmlow
  have hfix := hfixed β hβ n₁ n₂ m (linearNeumannDiagonalBaseMatrix S) hn₁ hn₂ hm hmQ
  have hident := fun Ω => linear_neumann_diagonal_centered_as_fixed_matrix_fluctuation Ω S
    ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
  have hn₁' : (0 : ℝ) < n₁ := by exact_mod_cast hn₁
  have hn₂' : (0 : ℝ) < n₂ := by exact_mod_cast hn₂
  have hNpos : (0 : ℝ) < (n₁ : ℝ) * (n₂ : ℝ) := by positivity
  have hp0 : 0 ≤ (m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)) := by positivity
  have hp1 : (m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)) ≤ 1 := by
    rw [div_le_one hNpos]; exact_mod_cast hm
  have hn1n : n₁ ≤ max n₁ n₂ := le_max_left _ _
  have hn2n : n₂ ≤ max n₁ n₂ := le_max_right _ _
  have hsup := mcSupBound S μ₁ (by linarith) hn₁ hn₂ hA1 (max n₁ n₂) hn1n hn2n
  generalize hn : max n₁ n₂ = n at hmQ hfix hmlow hn1n hn2n hsup ⊢
  generalize hp : (m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)) = p at hfix hident hp0 hp1 ⊢
  rcases Nat.lt_or_ge n 2 with hnlt | hn2
  · -- degenerate case `n = 1`: the right-hand side is `0`
    have hn1 : n = 1 := by omega
    subst hn1
    have h1 : Real.rpow ((1 : ℕ) : ℝ) (-β) = 1 := by simp
    rw [h1, one_mul, sub_self]
    exact mcEventNonneg p hp0 hp1 _
  · have hn2' : (2 : ℝ) ≤ n := by exact_mod_cast hn2
    have hnpos : (0 : ℝ) < n := by linarith
    have hlog : (1 : ℝ) / 2 ≤ Real.log n := by
      have := Real.one_sub_inv_le_log_of_pos hnpos
      have hinv : (n : ℝ)⁻¹ ≤ 1 / 2 := by
        rw [inv_eq_one_div]
        exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hn2'
      linarith
    have hlogpos : 0 < Real.log n := by linarith
    have hQpos : 0 < β * n * Real.log n := by positivity
    have hQn : (n : ℝ) ≤ β * n * Real.log n := by
      have : 1 ≤ β * Real.log n := by nlinarith
      nlinarith
    have hm0 : lam * μ₁ ^ 2 * r * (β * n * Real.log n) ≤ m := by
      have hmax : μ₁ ≤ max (Real.sqrt μ₀) μ₁ := le_max_right _ _
      calc lam * μ₁ ^ 2 * r * (β * n * Real.log n)
          = (lam * μ₁ * (n : ℝ) * r * (β * Real.log n)) * μ₁ := by ring
        _ ≤ (lam * μ₁ * (n : ℝ) * r * (β * Real.log n)) * max (Real.sqrt μ₀) μ₁ := by
            gcongr
        _ = lam * μ₁ * max (Real.sqrt μ₀) μ₁ * n * r * (β * Real.log n) := by ring
        _ ≤ m := hmlow
    have hm0pos : 0 < lam * μ₁ ^ 2 * r * (β * n * Real.log n) := by
      have hr' : (0 : ℝ) < r := by exact_mod_cast hr
      positivity
    have hmpos : (0 : ℝ) < m := lt_of_lt_of_le hm0pos hm0
    have hppos : 0 < p := by rw [← hp]; positivity
    -- the key deterministic inequality
    have hkey : p⁻¹ * (Cf * Real.sqrt ((β * n * Real.log n) / p) *
        (μ₁ * Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
          (μ₁ ^ 2 * (r : ℝ) * (2 * (n : ℝ)) / ((n₁ : ℝ) * (n₂ : ℝ))))) ≤
        2 * Cf * Real.rpow lam (-1) := by
      rw [Real.rpow_eq_pow, Real.rpow_neg_one]
      have hr' : (0 : ℝ) < r := by exact_mod_cast hr
      have hμ₁' : (0 : ℝ) < μ₁ := by linarith
      have hlam' : (0 : ℝ) < lam := by linarith
      set A := p⁻¹ * (Cf * Real.sqrt ((β * n * Real.log n) / p) *
        (μ₁ * Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
          (μ₁ ^ 2 * (r : ℝ) * (2 * (n : ℝ)) / ((n₁ : ℝ) * (n₂ : ℝ))))) with hA
      have hA0 : 0 ≤ A := by rw [hA]; positivity
      have hB0 : 0 ≤ 2 * Cf * lam⁻¹ := by positivity
      have hpN : p * ((n₁ : ℝ) * (n₂ : ℝ)) = m := by rw [← hp]; field_simp
      have hA2 : A ^ 2 = 4 * Cf ^ 2 * (β * n * Real.log n) * μ₁ ^ 6 * r ^ 3 * n ^ 2 / m ^ 3 := by
        rw [hA]
        have hs1 := Real.sq_sqrt (show (0 : ℝ) ≤ (β * n * Real.log n) / p by positivity)
        have hs2 := Real.sq_sqrt (show (0 : ℝ) ≤ (r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)) by positivity)
        rw [← hpN]
        field_simp
        rw [hs1, hs2]
        field_simp [hppos.ne', hn₁'.ne', hn₂'.ne']
        ring
      have hpoly : (β * n * Real.log n) * μ₁ ^ 6 * r ^ 3 * n ^ 2 * lam ^ 2 ≤ (m : ℝ) ^ 3 := by
        have hn2Q : (n : ℝ) ^ 2 ≤ (β * n * Real.log n) ^ 2 := pow_le_pow_left₀ hnpos.le hQn 2
        calc (β * n * Real.log n) * μ₁ ^ 6 * r ^ 3 * n ^ 2 * lam ^ 2
            ≤ (β * n * Real.log n) * μ₁ ^ 6 * r ^ 3 * (β * n * Real.log n) ^ 2 * lam ^ 2 := by
              gcongr
          _ ≤ (β * n * Real.log n) * μ₁ ^ 6 * r ^ 3 * (β * n * Real.log n) ^ 2 * lam ^ 2 * lam :=
              le_mul_of_one_le_right (by positivity) hlam
          _ = (lam * μ₁ ^ 2 * r * (β * n * Real.log n)) ^ 3 := by ring
          _ ≤ (m : ℝ) ^ 3 := pow_le_pow_left₀ hm0pos.le hm0 3
      have hA2le : A ^ 2 ≤ (2 * Cf * lam⁻¹) ^ 2 := by
        rw [hA2]
        have hm3 : (0 : ℝ) < m ^ 3 := by positivity
        rw [div_le_iff₀ hm3]
        calc 4 * Cf ^ 2 * (β * n * Real.log n) * μ₁ ^ 6 * r ^ 3 * n ^ 2
            = 4 * Cf ^ 2 * lam⁻¹ ^ 2 *
                ((β * n * Real.log n) * μ₁ ^ 6 * r ^ 3 * n ^ 2 * lam ^ 2) := by
              field_simp
          _ ≤ 4 * Cf ^ 2 * lam⁻¹ ^ 2 * (m : ℝ) ^ 3 := by gcongr
          _ = (2 * Cf * lam⁻¹) ^ 2 * (m : ℝ) ^ 3 := by ring
      nlinarith [hA2le, hA0, hB0]
    have himp : ∀ Ω : Finset (Fin n₁ × Fin n₂),
        CenteredSamplingSpectralBound Ω p (linearNeumannDiagonalBaseMatrix S)
          (Cf * Real.sqrt ((β * n * Real.log n) / p) *
            entrySupNorm (linearNeumannDiagonalBaseMatrix S)) →
        spectralNorm (linearNeumannDiagonalCenteredContribution Ω S p) ≤
          2 * Cf * Real.rpow lam (-1) := by
      intro Ω hΩ
      unfold CenteredSamplingSpectralBound at hΩ
      rw [hident Ω, mcSpectralSmul]
      have habs : |p⁻¹ * (1 - 2 * p)| ≤ p⁻¹ := by
        rw [abs_mul, abs_of_nonneg (inv_nonneg.mpr hp0)]
        have h12 : |1 - 2 * p| ≤ 1 := by
          rw [abs_le]; constructor <;> linarith
        calc p⁻¹ * |1 - 2 * p| ≤ p⁻¹ * 1 := by gcongr
          _ = p⁻¹ := mul_one _
      have hsn := mcSpectralNonneg (centeredSamplingFluctuation Ω p (linearNeumannDiagonalBaseMatrix S))
      calc |p⁻¹ * (1 - 2 * p)| *
            spectralNorm (centeredSamplingFluctuation Ω p (linearNeumannDiagonalBaseMatrix S))
          ≤ p⁻¹ * (Cf * Real.sqrt ((β * n * Real.log n) / p) *
              entrySupNorm (linearNeumannDiagonalBaseMatrix S)) :=
            mul_le_mul habs hΩ hsn (inv_nonneg.mpr hp0)
        _ ≤ p⁻¹ * (Cf * Real.sqrt ((β * n * Real.log n) / p) *
              (μ₁ * Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
                (μ₁ ^ 2 * (r : ℝ) * (2 * (n : ℝ)) / ((n₁ : ℝ) * (n₂ : ℝ))))) := by
            gcongr
        _ ≤ 2 * Cf * Real.rpow lam (-1) := hkey
    exact le_trans hfix (mcEventMono p hp0 hp1 _ _ himp)
