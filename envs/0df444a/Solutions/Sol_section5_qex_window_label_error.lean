-- Prove2me | solution 1 for section5_qex_window_label_error
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T20:37:33.424695+00:00
-- url     : https://prove2.me/submissions/bfe04b26-8810-4a82-84c4-add86ab24968

import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QAlgorithms_Defs_Gates
import Definitions.Def_QuantumLTF_Example_HermiteModel
import Definitions.Def_QuantumLTF_Example_qex
import Definitions.Def_QuantumLTF_Membership_Supplement_band1D53
import Definitions.Def_QuantumLTF_Membership_Supplement_bandKet
import Definitions.Def_QuantumLTF_Membership_Supplement_bandWeight
import Definitions.Def_QuantumLTF_Membership_Supplement_hermCoeff
import Definitions.Def_QuantumLTF_Membership_Supplement_projDist
import Definitions.Def_QuantumLTF_Membership_disagree
import Definitions.Def_QuantumLTF_Membership_flatReg
import Definitions.Def_QuantumLTF_Membership_ltf
import Definitions.Def_QuantumLTF_Membership_splitReg
import Definitions.Def_Section5Verified_Section5GridIsometry
import Definitions.Def_Section5Verified_Section5RealWindow
import Definitions.Def_Section5Verified_Section5SignedWindow
import Mathlib
import Theorems.Thm_section5_coordinate_approximation_norm
import Theorems.Thm_section5_gaussian_cube_tail
import Theorems.Thm_section5_gaussian_inner_strip
import Theorems.Thm_section5_qex_gaussian_probability_transfer
import Theorems.Thm_section5_real_window_error
import Theorems.Thm_section5_roundCoord_error
import Theorems.Thm_section5_rounding_label_probability
section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory QuantumLTF.Membership QuantumLTF.Example





theorem section5_sgn_change_strip (a b : ℝ) (h : sgn a ≠ sgn b) : |a| ≤ |a-b| := by
  unfold sgn at h
  split_ifs at h with ha hb hb
  · exact False.elim (h rfl)
  · rw [abs_of_nonneg ha, abs_of_nonneg (by linarith : 0 ≤ a-b)]
    linarith
  · rw [abs_of_nonpos (by linarith : a ≤ 0), abs_of_nonpos (by linarith : a-b ≤ 0)]
    linarith
  · exact False.elim (h rfl)

















end
section
set_option autoImplicit false

open MeasureTheory ProbabilityTheory QuantumLTF.Membership QuantumLTF.Example

/-! Gaussian orientation errors after coordinate rounding, using the mission's already-Proved
Gaussian disagreement lemma (Lemma 2.1), with its accepted proof checked locally. -/

theorem section5_ltf_measurable {n : ℕ} (w : EuclideanSpace ℝ (Fin n)) (θ : ℝ) :
    Measurable (ltf w θ) := by
  unfold ltf sgn
  exact Measurable.ite (measurableSet_le measurable_const (by fun_prop))
    measurable_const measurable_const









end
section
set_option autoImplicit false

open MeasureTheory ProbabilityTheory QuantumLTF.Membership QuantumLTF.Example

/-! Gaussian halfspace stability for a coordinate approximation on a bounded window. -/

theorem section5_approximation_label_strip {n : ℕ}
    (w x y : EuclideanSpace ℝ (Fin n)) (hw : ‖w‖=1) (τ : ℝ)
    (hxy : ‖x-y‖ ≤ τ) (hlabel : ltf w 0 x ≠ ltf w 0 y) :
    |inner ℝ w x| ≤ τ := by
  have hs := section5_sgn_change_strip (inner ℝ w x) (inner ℝ w y)
    (by simpa [ltf] using hlabel)
  have hi : |inner ℝ w x-inner ℝ w y| ≤ ‖x-y‖ := by
    rw [← inner_sub_right]
    simpa [hw] using norm_inner_le_norm (𝕜:=ℝ) w (x-y)
  exact hs.trans (hi.trans hxy)

theorem section5_window_label_probability {n : ℕ}
    (w : EuclideanSpace ℝ (Fin n)) (hw : ‖w‖=1)
    (Q : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (S : Set (EuclideanSpace ℝ (Fin n))) (τ : ℝ) (hτ : 0 ≤ τ)
    (happrox : ∀ x ∈ S, ‖x-Q x‖ ≤ τ) :
    (stdGaussian (EuclideanSpace ℝ (Fin n))).real {x | ltf w 0 x ≠ ltf w 0 (Q x)} ≤
      (stdGaussian (EuclideanSpace ℝ (Fin n))).real Sᶜ +
        2*τ/Real.sqrt (2*Real.pi) := by
  let μ := stdGaussian (EuclideanSpace ℝ (Fin n))
  have hsub : {x | ltf w 0 x ≠ ltf w 0 (Q x)} ⊆
      Sᶜ ∪ {x | |inner ℝ w x| ≤ τ} := by
    intro x hx
    by_cases hs : x ∈ S
    · exact Or.inr (section5_approximation_label_strip w x (Q x) hw τ (happrox x hs) hx)
    · exact Or.inl hs
  exact (measureReal_mono (μ:=μ) hsub).trans
    ((measureReal_union_le _ _).trans (add_le_add (le_refl _)
      (section5_gaussian_inner_strip w hw τ hτ)))



theorem section5_coordinate_window_label_probability {n : ℕ}
    (w : EuclideanSpace ℝ (Fin n)) (hw : ‖w‖=1)
    (Q : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (S : Set (EuclideanSpace ℝ (Fin n))) (δ : ℝ) (hδ : 0 ≤ δ)
    (happrox : ∀ x ∈ S, ∀ i, |x i-Q x i| ≤ δ) :
    (stdGaussian (EuclideanSpace ℝ (Fin n))).real {x | ltf w 0 x ≠ ltf w 0 (Q x)} ≤
      (stdGaussian (EuclideanSpace ℝ (Fin n))).real Sᶜ +
        2*(δ*Real.sqrt n)/Real.sqrt (2*Real.pi) := by
  exact section5_window_label_probability w hw Q S _ (by positivity)
    (fun x hx => section5_coordinate_approximation_norm x (Q x) δ hδ (happrox x hx))

theorem section5_euclidean_gaussian_cube_tail (n : ℕ) (L : ℝ) (hL : 0 ≤ L) :
    (stdGaussian (EuclideanSpace ℝ (Fin n))).real
      {x : EuclideanSpace ℝ (Fin n) | ∃ i, L ≤ |x i|} ≤
        2*n*Real.exp (-L^2/2) := by
  have hmap : (Measure.pi (fun _ : Fin n => gaussianReal 0 1)).map (WithLp.toLp 2)=
      stdGaussian (EuclideanSpace ℝ (Fin n)) := map_pi_eq_stdGaussian
  rw [← hmap,map_measureReal_apply (WithLp.measurable_toLp 2 (Fin n → ℝ)) (by measurability)]
  exact section5_gaussian_cube_tail n L hL

theorem section5_cube_window_label_probability {n : ℕ}
    (w : EuclideanSpace ℝ (Fin n)) (hw : ‖w‖=1)
    (Q : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (L δ : ℝ) (hL : 0 ≤ L) (hδ : 0 ≤ δ)
    (happrox : ∀ x : EuclideanSpace ℝ (Fin n), (∀ i, |x i| < L) →
      ∀ i, |x i-Q x i| ≤ δ) :
    (stdGaussian (EuclideanSpace ℝ (Fin n))).real {x | ltf w 0 x ≠ ltf w 0 (Q x)} ≤
      2*n*Real.exp (-L^2/2)+2*(δ*Real.sqrt n)/Real.sqrt (2*Real.pi) := by
  let S : Set (EuclideanSpace ℝ (Fin n)) := {x | ∀ i, |x i| < L}
  have htail : (stdGaussian (EuclideanSpace ℝ (Fin n))).real Sᶜ ≤
      2*n*Real.exp (-L^2/2) := by
    have heq : Sᶜ={x : EuclideanSpace ℝ (Fin n) | ∃ i, L ≤ |x i|} := by
      ext x
      simp [S,not_forall]
    rw [heq]
    exact section5_euclidean_gaussian_cube_tail n L hL
  exact (section5_coordinate_window_label_probability w hw Q S δ hδ happrox).trans
    (add_le_add htail (le_refl _))

end
section
set_option autoImplicit false

open MeasureTheory ProbabilityTheory QAlgorithms QuantumLTF.Example QuantumLTF.Membership

/-! A complete finite-QEX error estimate for discarding high and low coordinate bits. -/

theorem section5_real_window_measurable (P H : ℤ) (δ : ℝ) :
    Measurable (section5_real_window P H δ) := by
  unfold section5_real_window
  exact measurable_const.mul ((measurable_of_countable _).comp (by fun_prop))

theorem section5_real_window_vec_measurable (n : ℕ) (P H : ℤ) (δ : ℝ) :
    Measurable (section5_real_window_vec (n:=n) P H δ) := by
  unfold section5_real_window_vec
  apply (WithLp.measurable_toLp 2 (Fin n → ℝ)).comp
  exact measurable_pi_lambda _ (fun i => (section5_real_window_measurable P H δ).comp (by fun_prop))

theorem section5_rounded_real_window_error (M : ℕ) (hM : 1 ≤ M)
    (P H : ℤ) (hP : 0 < P) (hH : 0 < H) (x : ℝ)
    (hx : |x| < gridSpacing M*H*P-gridSpacing M) :
    |x-section5_real_window P H (gridSpacing M) (roundCoord M x)| < gridSpacing M*(P+2) := by
  have hδ : 0 < gridSpacing M := section5_gridSpacing_positive M (by omega)
  have hround := section5_roundCoord_error hM x
  have hx' : |roundCoord M x| < gridSpacing M*H*P := by
    have hh := abs_sub_le (roundCoord M x) x 0
    rw [sub_zero,sub_zero,abs_sub_comm (roundCoord M x) x] at hh
    linarith
  have he := section5_real_window_error P H hP hH (gridSpacing M) hδ (roundCoord M x) hx'
  calc
    _ ≤ |x-roundCoord M x|+
        |roundCoord M x-section5_real_window P H (gridSpacing M) (roundCoord M x)| := abs_sub_le _ _ _
    _ < gridSpacing M+gridSpacing M*(P+1) := add_lt_add_of_le_of_lt hround he
    _ = _ := by ring

theorem section5_rounded_window_gaussian_error {n M : ℕ} (hM : 1 ≤ M)
    (u : EuclideanSpace ℝ (Fin n)) (hu : ‖u‖=1)
    (P H : ℤ) (hP : 0 < P) (hH : 0 < H) :
    (stdGaussian (EuclideanSpace ℝ (Fin n))).real
      {x | ltf u 0 (roundVec M x) ≠
        ltf u 0 (section5_real_window_vec P H (gridSpacing M) (roundVec M x))} ≤
          Real.sqrt (8*n/M)+
          2*n*Real.exp (-(gridSpacing M*H*P-gridSpacing M)^2/2)+
          2*((gridSpacing M*(P+2))*Real.sqrt n)/Real.sqrt (2*Real.pi) := by
  let μ := stdGaussian (EuclideanSpace ℝ (Fin n))
  let Q := fun x : EuclideanSpace ℝ (Fin n) =>
    section5_real_window_vec P H (gridSpacing M) (roundVec M x)
  let A := {x | ltf u 0 x ≠ ltf u 0 (roundVec M x)}
  let B := {x | ltf u 0 x ≠ ltf u 0 (Q x)}
  have hsub : {x | ltf u 0 (roundVec M x) ≠ ltf u 0 (Q x)} ⊆ A ∪ B := by
    intro x hx
    by_contra h
    simp only [A,B,Set.mem_union,Set.mem_ofPred_eq,not_or,not_not] at h
    exact hx (h.1.symm.trans h.2)
  have hδ : 0 < gridSpacing M := section5_gridSpacing_positive M (by omega)
  have hHP : (1:ℝ) ≤ (H:ℝ)*P := by
    have hh : (1:ℤ) ≤ H*P := by nlinarith
    exact_mod_cast hh
  have hL : 0 ≤ gridSpacing M*H*P-gridSpacing M := by nlinarith
  have hB := section5_cube_window_label_probability u hu Q
    (gridSpacing M*H*P-gridSpacing M) (gridSpacing M*(P+2)) hL (by positivity)
    (fun x hx i => (section5_rounded_real_window_error M hM P H hP hH (x i) (hx i)).le)
  have hA := section5_rounding_label_probability hM u hu
  calc
    _ ≤ μ.real (A ∪ B) := measureReal_mono hsub
    _ ≤ μ.real A+μ.real B := measureReal_union_le _ _
    _ ≤ _ := by linarith



end
set_option autoImplicit false
open MeasureTheory ProbabilityTheory QAlgorithms QuantumLTF.Example QuantumLTF.Membership
open Classical in
theorem solution {n q : ℕ} (hq : 0 < q)
    (hsize : 128*(n:ℝ)^2 ≤ (2:ℝ)^q)
    (u : EuclideanSpace ℝ (Fin n)) (hu : ‖u‖=1)
    (P H : ℤ) (hP : 0 < P) (hH : 0 < H) :
    (∑ z : Qubits (n*q),
      if ltf u 0 (gridPoint z) ≠
          ltf u 0 (section5_real_window_vec P H (gridSpacing (2^q)) (gridPoint z)) then
        gridWeight z/(∑ y : Qubits (n*q), gridWeight y) else 0) ≤
      Real.sqrt (8*n/(2:ℝ)^q)+
      2*n*Real.exp (-(gridSpacing (2^q)*H*P-gridSpacing (2^q))^2/2)+
      2*((gridSpacing (2^q)*(P+2))*Real.sqrt n)/Real.sqrt (2*Real.pi)+
      (8*n*Real.sqrt (32/(2:ℝ)^q)+4*Real.sqrt (2*n)*Real.exp (-Real.pi*(2:ℝ)^q/4)) := by
  let S := {x : EuclideanSpace ℝ (Fin n) | ltf u 0 x ≠
    ltf u 0 (section5_real_window_vec P H (gridSpacing (2^q)) x)}
  have hS : MeasurableSet S := (measurableSet_eq_fun (section5_ltf_measurable u 0)
    ((section5_ltf_measurable u 0).comp (section5_real_window_vec_measurable n P H _))).compl
  have hh := section5_qex_gaussian_probability_transfer n q hq hsize S hS
  have hsum : (∑ z : Qubits (n*q), @ite ℝ (gridPoint z ∈ S) (Classical.propDecidable _)
      (gridWeight z/(∑ y : Qubits (n*q), gridWeight y)) 0)=
      ∑ z : Qubits (n*q), if ltf u 0 (gridPoint z) ≠
        ltf u 0 (section5_real_window_vec P H (gridSpacing (2^q)) (gridPoint z)) then
          gridWeight z/(∑ y : Qubits (n*q), gridWeight y) else 0 := by
    apply Finset.sum_congr rfl
    intro z hz
    by_cases hh : ltf u 0 (gridPoint z)=
        ltf u 0 (section5_real_window_vec P H (gridSpacing (2^q)) (gridPoint z)) <;> simp [S,hh]
  rw [hsum] at hh
  have hgauss := section5_rounded_window_gaussian_error (M:=2^q) Nat.one_le_two_pow u hu P H hP hH
  have hupper := (abs_le.mp hh).2
  dsimp only [S,Set.mem_ofPred_eq] at hupper
  simp only [Nat.cast_pow,Nat.cast_ofNat] at hgauss
  apply (sub_le_iff_le_add.mp hupper).trans
  linarith only [hgauss]
