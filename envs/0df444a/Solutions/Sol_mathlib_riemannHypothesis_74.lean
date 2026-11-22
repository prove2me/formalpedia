-- Prove2me | solution 74 for mathlib_riemannHypothesis
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T22:30:40.002803+00:00
-- url     : https://prove2.me/submissions/5e939821-2818-48cf-9357-cd3d05445676
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_MasulloRH_GaussianThetaApproximation
import Theorems.Thm_MasulloRH_cofinal_rational_theta_gram_interval_tables
import Theorems.Thm_MasulloRH_finite_theta_approximation_excludes_rectangle_zeros
import Theorems.Thm_MasulloRH_rational_theta_cutoff_trace_defect
import Theorems.Thm_MasulloRH_rational_theta_annihilator_jet_trace
import Theorems.Thm_MasulloRH_regularized_test_admissible
import Theorems.Thm_riemannHypothesis_iff_zeros_in_strip_on_line
import Theorems.Thm_MasulloAudit_trace_formula_rational_one_sided_window_iff
import Theorems.Thm_MasulloRH_trace_window_comparison
import Theorems.Thm_MasulloAudit_one_sided_regular_windows_iff_RH

-- Step 1: `MasulloRH.cofinal_rational_theta_gram_interval_tables` implies `MasulloRH.cofinal_rational_theta_gram_certificates` (accepted reduction of `MasulloRH.cofinal_rational_theta_gram_certificates`).
section

open MasulloRH MasulloRH.GaussianApproximation MeasureTheory Finset
open scoped BigOperators ComplexConjugate

private theorem quadratic_re_le_of_entry_error {ι : Type} [Fintype ι]
    (A Q : ι → ι → ℂ) (d : ι → ℂ) (η : ℝ) (hη : 0 ≤ η)
    (hentry : ∀ i j, ‖A i j-Q i j‖ ≤ η) :
    (∑ i, ∑ j, conj (d i)*d j*A i j).re ≤
      (∑ i, ∑ j, conj (d i)*d j*Q i j).re +
        η * (∑ i, (|(d i).re|+|(d i).im|))^2 := by
  classical
  have hdiff : (∑ i, ∑ j, conj (d i)*d j*A i j) -
      (∑ i, ∑ j, conj (d i)*d j*Q i j) =
      ∑ i, ∑ j, conj (d i)*d j*(A i j-Q i j) := by
    simp only [mul_sub, Finset.sum_sub_distrib]
  have hn : ‖(∑ i, ∑ j, conj (d i)*d j*A i j) -
      (∑ i, ∑ j, conj (d i)*d j*Q i j)‖ ≤ η * (∑ i, ‖d i‖)^2 := by
    rw [hdiff]
    calc
      _ ≤ ∑ i, ‖∑ j, conj (d i)*d j*(A i j-Q i j)‖ := norm_sum_le _ _
      _ ≤ ∑ i, ∑ j, ‖conj (d i)*d j*(A i j-Q i j)‖ :=
        Finset.sum_le_sum (fun i _ => norm_sum_le _ _)
      _ ≤ ∑ i, ∑ j, ‖d i‖*‖d j‖*η := by
        apply Finset.sum_le_sum
        intro i hi
        apply Finset.sum_le_sum
        intro j hj
        rw [norm_mul, norm_mul, Complex.norm_conj]
        exact mul_le_mul_of_nonneg_left (hentry i j) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      _ = ((∑ i, ‖d i‖)*(∑ j, ‖d j‖))*η := by
        simp only [Finset.sum_mul, Finset.mul_sum, mul_assoc]
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ = η * (∑ i, ‖d i‖)^2 := by ring
  have hl1 : (∑ i, ‖d i‖)^2 ≤ (∑ i, (|(d i).re|+|(d i).im|))^2 := by
    apply (sq_le_sq₀ (Finset.sum_nonneg (fun i _ => norm_nonneg _))
      (Finset.sum_nonneg (fun i _ => add_nonneg (abs_nonneg _) (abs_nonneg _)))).mpr
    exact Finset.sum_le_sum (fun i _ => Complex.norm_le_abs_re_add_abs_im (d i))
  have hb := hn.trans (mul_le_mul_of_nonneg_left hl1 hη)
  have hr := Complex.re_le_norm ((∑ i, ∑ j, conj (d i)*d j*A i j) -
      (∑ i, ∑ j, conj (d i)*d j*Q i j))
  rw [Complex.sub_re] at hr
  linarith

theorem MasulloRH.cofinal_rational_theta_gram_certificates :
    ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ ∃ (m : ℕ) (a : Fin m → ℚ × ℚ) (y : Fin m → ℚ),
      let δ : ℝ := 1/(16*((n:ℝ)+1))
      energy (3/4) (1/4-δ) (residual n
         (fun i => ((a i).1 : ℂ) + ((a i).2 : ℂ)*Complex.I) (fun i => (y i : ℝ))) <
          δ * Real.exp (-(1/2:ℝ)) := by
  intro N
  obtain ⟨n,hn,m,a,y,R,η,hη,hrest⟩ := cofinal_rational_theta_gram_interval_tables N
  refine ⟨n,hn,m,a,y,?_⟩
  let δ : ℝ := 1/(16*((n:ℝ)+1))
  let u : Fin (m+1) → ℝ → ℂ := Fin.cons (pulse n)
    (fun i x => theta (x-(y i:ℝ)))
  let d : Fin (m+1) → ℂ := Fin.cons 1
    (fun i => -(((a i).1:ℂ)+((a i).2:ℂ)*Complex.I))
  let A : Fin (m+1) → Fin (m+1) → ℂ := fun i j =>
    ∫ x : ℝ, (Real.exp (2*(3/4)*x+2*(1/4-δ)*|x|):ℂ)*conj (u i x)*u j x
  let Q : Fin (m+1) → Fin (m+1) → ℂ := fun i j =>
    ((R i j).1:ℂ)+((R i j).2:ℂ)*Complex.I
  have hentry : ∀ i j, ‖A i j-Q i j‖ ≤ (η:ℝ) := hrest.1
  have hcert : (∑ i, ∑ j, conj (d i)*d j*Q i j).re +
      (η:ℝ)*(∑ i, (|(d i).re|+|(d i).im|))^2 < δ/2 := hrest.2
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hηr : 0 ≤ (η:ℝ) := by exact_mod_cast hη
  have hfull := finite_theta_approximation_excludes_rectangle_zeros.1 m (n:ℝ)
    (3/4) (1/4-δ) δ
    (fun i => ((a i).1:ℂ)+((a i).2:ℂ)*Complex.I) (fun i => (y i:ℝ))
    (Nat.cast_nonneg n) hδ (by linarith) (by linarith)
  have henergy : energy (3/4) (1/4-δ) (residual n
      (fun i => ((a i).1:ℂ)+((a i).2:ℂ)*Complex.I) (fun i => (y i:ℝ))) =
      (∑ i, ∑ j, conj (d i)*d j*A i j).re := hfull.2.2.1
  change energy (3/4) (1/4-δ) (residual n
      (fun i => ((a i).1:ℂ)+((a i).2:ℂ)*Complex.I) (fun i => (y i:ℝ))) <
        δ*Real.exp (-(1/2:ℝ))
  rw [henergy]
  apply lt_of_lt_of_le ((quadratic_re_le_of_entry_error A Q d (η:ℝ) hηr hentry).trans_lt hcert)
  have he : (1/2:ℝ) ≤ Real.exp (-(1/2:ℝ)) := by
    linarith [Real.add_one_le_exp (-(1/2:ℝ))]
  have h := mul_le_mul_of_nonneg_left he hδ.le
  nlinarith

end

-- Step 2: `MasulloRH.cofinal_rational_theta_gram_certificates` implies `MasulloRH.rational_theta_cutoff_trace_lower_bound` (accepted reduction of `MasulloRH.rational_theta_cutoff_trace_lower_bound`).
section

open MasulloRH MasulloGRH Filter MeasureTheory
open scoped Topology InnerProductSpace

theorem MasulloRH.rational_theta_cutoff_trace_lower_bound :
    ∀ ε : ℝ, 0 < ε → ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧
      ∀ T : rationalThetaAnnihilator ((n:ℝ)+1) →L[ℂ] rationalThetaAnnihilator ((n:ℝ)+1),
        IsRationalThetaConvolution ((n:ℝ)+1) (regularizedTraceTest n 3) T →
          (cutoffPolar n 3 - (cutoffArch n 3 + cutoffPrime n 3)).re ≤
            (operatorTrace T).re + ε := by
  classical
  have hRH := finite_theta_approximation_excludes_rectangle_zeros.2
    cofinal_rational_theta_gram_certificates
  have he (n : ℕ) : ∃ T : rationalThetaAnnihilator ((n:ℝ)+1) →L[ℂ] rationalThetaAnnihilator ((n:ℝ)+1),
      IsRationalThetaConvolution ((n:ℝ)+1) (regularizedTraceTest n 3) T := by
    obtain ⟨T,hT,_⟩ := (rational_theta_annihilator_jet_trace ((n:ℝ)+1)
      (by linarith [Nat.cast_nonneg (α:=ℝ) n])).2 _ (regularized_test_admissible n 3)
    exact ⟨T,hT.1⟩
  choose T hT using he
  obtain ⟨hlim,_,hiff⟩ := rational_theta_cutoff_trace_defect T hT
  rw [hiff.mpr hRH] at hlim
  intro ε hε N
  obtain ⟨m,hm⟩ := eventually_atTop.mp (hlim.eventually_lt_const hε)
  let n := max N m
  refine ⟨n,le_max_left _ _,?_⟩
  intro S hS
  have hEq : S = T n := by
    apply ContinuousLinearMap.ext
    intro u
    apply Subtype.ext
    apply ext_inner_left ℂ
    intro v
    exact (hS u v).trans ((hT n u v).symm)
  rw [hEq]
  have h := hm n (le_max_right _ _)
  linarith

end

-- Step 3: `MasulloRH.rational_theta_cutoff_trace_lower_bound` implies `MasulloRH.cofinal_one_sided_trace_windows` (accepted reduction of `MasulloRH.cofinal_one_sided_trace_windows`).
section

open MasulloRH MasulloGRH MeasureTheory Set Filter
open scoped Topology

theorem MasulloRH.cofinal_one_sided_trace_windows (n : ℕ) :
    ∃ α : ℝ, 0 < α ∧ α ≤ 1 / (n + 1 : ℝ) ∧
      ∀ φ : ℝ → ℂ, IsRationalTraceTest φ → tsupport φ ⊆ Ioi 1 →
      (∫ t in Ioi (1 : ℝ), realTraceIntegrand φ t) +
        (∑' i : Nat.Primes × ℕ, primePowerTraceTerm φ i) =
      mellin φ (1/2) + mellin φ (-1/2) -
        ∑' ρ : ZetaZerosInTraceStrip α, zetaTraceTerm φ α ρ := by
  classical
  have existsT (j : ℕ) : ∃ T : rationalThetaAnnihilator ((j:ℝ)+1) →L[ℂ] rationalThetaAnnihilator ((j:ℝ)+1),
      IsRationalThetaConvolution ((j:ℝ)+1) (regularizedTraceTest j 3) T := by
    obtain ⟨T,hT,_⟩ := (rational_theta_annihilator_jet_trace ((j:ℝ)+1)
      (by linarith [Nat.cast_nonneg (α:=ℝ) j])).2 _ (regularized_test_admissible j 3)
    exact ⟨T,hT.1⟩
  choose T hT using existsT
  let D := ∑' z : {z : ZetaZerosInTraceStrip (1/2) // z.val.re ≠ 1/2},
    (zeroResolventTerm (1/2) 3 z.val).re
  obtain ⟨hlim,hpos,hiff⟩ := rational_theta_cutoff_trace_defect T hT
  have hnonpos : D ≤ 0 := by
    by_contra! hD
    have he : 0 < D/2 := by linarith
    have hlarge := (tendsto_order.mp hlim).1 (D/2) (show D/2 < D by linarith)
    obtain ⟨N,hN⟩ := eventually_atTop.1 hlarge
    obtain ⟨j,hj,hjT⟩ := rational_theta_cutoff_trace_lower_bound (D/2) he N
    have hu := hjT (T j) (hT j)
    have hl := hN j hj
    linarith
  have hRH : RiemannHypothesis := hiff.mp (le_antisymm hnonpos hpos)
  let α := 1 / (n+1:ℝ)
  have hα : 0 < α := by dsimp [α]; positivity
  refine ⟨α,hα,le_rfl,fun φ hφ hsupport => ?_⟩
  have hline (ρ : ZetaZerosInTraceStrip (1/2)) : |ρ.val.re - 1/2| < α := by
    have h := riemannHypothesis_iff_zeros_in_strip_on_line.mp hRH ρ.val
      ρ.property.1 ρ.property.2.1 ρ.property.2.2.1
    simpa [h] using hα
  exact ((MasulloAudit.trace_formula_rational_one_sided_window_iff α hα).2 hline φ hφ hsupport).2.2.2

end

-- Step 4: `MasulloRH.cofinal_one_sided_trace_windows` implies `MasulloRH.regular_width_one_sided_trace` (accepted reduction of `MasulloRH.regular_width_one_sided_trace`).
section

-- New proof-sketch for the Masullo mission's regular-width frontier.




open MasulloRH MeasureTheory Set Filter Topology

theorem MasulloRH.regular_width_one_sided_trace (β : ℝ) (hβ : 0 < β)
    (hreg : ∀ ρ : ZetaZerosInTraceStrip (1/2), |ρ.val.re - 1/2| ≠ β)
    (φ : ℝ → ℂ) (hφ : IsRationalTraceTest φ) (hpos : tsupport φ ⊆ Ioi 1) :
    (∫ t in Ioi (1 : ℝ), realTraceIntegrand φ t) +
        (∑' i : Nat.Primes × ℕ, primePowerTraceTerm φ i) =
      mellin φ (1/2) + mellin φ (-1/2) -
        ∑' ρ : ZetaZerosInTraceStrip β, zetaTraceTerm φ β ρ := by
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hβ
  obtain ⟨α, ha, han, htrace⟩ := cofinal_one_sided_trace_windows n
  have inside := (MasulloAudit.trace_formula_rational_one_sided_window_iff α ha).mp
    (fun f hf hs ↦ by
      have c := trace_window_comparison α f hf
      exact ⟨c.1, c.2.1, c.2.2.1, htrace f hf hs⟩)
  have wider := (MasulloAudit.trace_formula_rational_one_sided_window_iff β hβ).mpr
    (fun ρ ↦ (inside ρ).trans (lt_of_le_of_lt han hn))
  exact (wider φ hφ hpos).2.2.2

end

-- Step 5: `MasulloRH.regular_width_one_sided_trace` implies `RiemannHypothesis` (accepted reduction of `mathlib_riemannHypothesis`).
section

theorem solution : RiemannHypothesis :=
  MasulloAudit.one_sided_regular_windows_iff_RH.mp
    (fun β hβ hreg φ hφ hpos =>
      MasulloRH.regular_width_one_sided_trace β hβ hreg φ hφ hpos)

end
