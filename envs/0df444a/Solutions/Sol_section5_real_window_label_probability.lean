-- Prove2me | solution 1 for section5_real_window_label_probability
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T20:13:36.249687+00:00
-- url     : https://prove2.me/submissions/f9d1347c-6ef8-469a-986f-455b66fa6bc4

import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QuantumLTF_Example_HermiteModel
import Definitions.Def_QuantumLTF_Membership_Supplement_band1D53
import Definitions.Def_QuantumLTF_Membership_Supplement_bandKet
import Definitions.Def_QuantumLTF_Membership_Supplement_bandWeight
import Definitions.Def_QuantumLTF_Membership_Supplement_hermCoeff
import Definitions.Def_QuantumLTF_Membership_Supplement_projDist
import Definitions.Def_QuantumLTF_Membership_flatReg
import Definitions.Def_QuantumLTF_Membership_splitReg
import Definitions.Def_Section5Verified_Section5RealWindow
import Mathlib
import Theorems.Thm_section5_coordinate_approximation_norm
import Theorems.Thm_section5_gaussian_cube_tail
import Theorems.Thm_section5_gaussian_inner_strip
import Theorems.Thm_section5_real_window_error
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
set_option autoImplicit false
open MeasureTheory ProbabilityTheory QuantumLTF.Membership QuantumLTF.Example
theorem solution {n : ℕ}
    (w : EuclideanSpace ℝ (Fin n)) (hw : ‖w‖=1)
    (P H : ℤ) (hP : 0 < P) (hH : 0 < H) (δ : ℝ) (hδ : 0 < δ) :
    (stdGaussian (EuclideanSpace ℝ (Fin n))).real
      {x | ltf w 0 x ≠ ltf w 0 (section5_real_window_vec P H δ x)} ≤
        2*n*Real.exp (-(δ*H*P)^2/2)+
          2*((δ*(P+1))*Real.sqrt n)/Real.sqrt (2*Real.pi) := by
  apply section5_cube_window_label_probability w hw _ (δ*H*P) (δ*(P+1))
    (by positivity) (by positivity)
  intro x hx i
  exact (section5_real_window_error P H hP hH δ hδ (x i) (hx i)).le
