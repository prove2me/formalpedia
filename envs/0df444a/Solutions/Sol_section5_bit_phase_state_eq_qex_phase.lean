-- Prove2me | solution 1 for section5_bit_phase_state_eq_qex_phase
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T20:06:06.382355+00:00
-- url     : https://prove2.me/submissions/d2b57f5d-0bf7-4320-8b60-c8591be36118

import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QAlgorithms_Defs_Gates
import Definitions.Def_QuantumLTF_Example_HermiteModel
import Definitions.Def_QuantumLTF_Example_qex
import Definitions.Def_QuantumLTF_Membership_Supplement_band1D53
import Definitions.Def_QuantumLTF_Membership_Supplement_bandKet
import Definitions.Def_QuantumLTF_Membership_Supplement_bandWeight
import Definitions.Def_QuantumLTF_Membership_Supplement_hermCoeff
import Definitions.Def_QuantumLTF_Membership_Supplement_projDist
import Definitions.Def_QuantumLTF_Membership_flatReg
import Definitions.Def_QuantumLTF_Membership_splitReg
import Definitions.Def_Section5Verified_Section5ExamplePhase
import Definitions.Def_Section5Verified_Section5FiniteCoefficientTransfer
import Definitions.Def_Section5Verified_Section5GaussianTail
import Definitions.Def_Section5Verified_Section5GridIsometry
import Definitions.Def_Section5Verified_Section5HermiteFoundations
import Definitions.Def_Section5Verified_Section5PhaseStateError
import Definitions.Def_Section5Verified_Section5PhysicalHermiteGrid
import Mathlib
import Theorems.Thm_section5_grid_exp_sum
namespace «Aux_w_53_hermite»
end «Aux_w_53_hermite»
section
set_option autoImplicit false

open MeasureTheory QAlgorithms QuantumLTF.Example Aux_w_53_hermite

/-! Matching the exact physical Hermite grid normalization and bit convention. -/









theorem section5_scalarGrid_grid_node {q : ℕ} (hq : 0 < q) (z : Qubits q) :
    scalarGrid z = -gridRadius (2^q)+(bitsEquivFin q z : ℝ)*gridSpacing (2^q) := by
  rcases q with _ | q
  · omega
  simp only [scalarGrid,gridRadius,gridSpacing,bitsEquivFin_apply,QuantumLTF.Example.bitsValue,
    bitsToNat,Nat.add_sub_cancel,pow_succ,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]
  ring













end
namespace «Aux_w_53_hermite»
end «Aux_w_53_hermite»
section
set_option autoImplicit false

open MeasureTheory QAlgorithms QuantumLTF.Example QuantumLTF.Membership Aux_w_53_hermite

/-! The sampled phase vector is exactly the phase branch of the public QEX state. -/

theorem section5_normalize_positive_amplitudes {ι : Type*} [Fintype ι]
    (u : ι → ℂ) (A : ι → ℝ) (hu : ∀ i, ‖u i‖=1) (hA : ∀ i, 0 ≤ A i) (i : ι) :
    NormedSpace.normalize (WithLp.toLp 2 (fun j => u j*(A j : ℂ)) : EuclideanSpace ℂ ι) i =
      u i*(Real.sqrt ((A i)^2/∑ j, (A j)^2) : ℂ) := by
  let v : EuclideanSpace ℂ ι := WithLp.toLp 2 (fun j => u j*(A j : ℂ))
  have hN : ‖v‖^2 = ∑ j, (A j)^2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp only [v,norm_mul,hu,one_mul,Complex.norm_real,Real.norm_eq_abs,sq_abs]
  have hroot : Real.sqrt (∑ j, (A j)^2) = ‖v‖ := by
    rw [← hN,Real.sqrt_sq (norm_nonneg v)]
  rw [Real.sqrt_div (sq_nonneg _),Real.sqrt_sq (hA i),hroot]
  change (‖v‖⁻¹ : ℝ) • (u i*(A i:ℂ)) = u i*((A i/‖v‖:ℝ):ℂ)
  simp only [Complex.real_smul,Complex.ofReal_div,Complex.ofReal_inv]
  ring



theorem section5_gridPoint_flatReg {n q : ℕ} (z : Fin n → Qubits q) :
    gridPoint (flatReg n q z) = WithLp.toLp 2 (fun i => scalarGrid (z i)) := by
  have hflat (i : Fin n) : (fun j : Fin q => flatReg n q z
      ⟨i.val*q+j.val,by nlinarith [Nat.mul_le_mul_right q (Nat.succ_le_iff.mpr i.isLt),j.isLt]⟩) = z i := by
    funext j
    simpa only [flatReg,finProdFinEquiv,Equiv.coe_fn_mk,Nat.add_comm,Nat.mul_comm] using
      congrArg (fun p : Fin n × Fin q => z p.1 p.2) (finProdFinEquiv.symm_apply_apply (i,j))
  simp only [gridPoint,scalarGrid,hflat]

theorem section5_gaussian_density_exp (n : ℕ) (x : Fin n → ℝ) :
    section5_gaussian_density n x = (Real.sqrt (2*Real.pi))⁻¹^n *
      Real.exp (-‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin n))‖^2/2) := by
  unfold section5_gaussian_density
  simp_rw [phi_def]
  rw [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin,
    ← Real.exp_sum,EuclideanSpace.norm_sq_eq]
  congr 2
  simp only [Real.norm_eq_abs,sq_abs,Finset.sum_neg_distrib,Finset.sum_div,neg_div]

theorem section5_grid_phase_as_positive_amplitudes {n : ℕ} (w : EuclideanSpace ℝ (Fin n)) (M : ℕ) :
    section5_grid_vector n M (section5_ideal_phase_state w) =
      WithLp.toLp 2 (fun j => section5_ltf_phase w (section5_grid_node n M j)*
        ((Real.sqrt ((gridSpacing M)^n)*
          ∏ i, Real.sqrt (phi (section5_grid_node n M j i)) : ℝ) : ℂ)) := by
  ext j
  simp only [section5_grid_vector,section5_ideal_phase_state,section5_gaussian_amplitude,
    Complex.ofReal_mul]
  ring

theorem section5_grid_phase_amplitude_sq (n M : ℕ) (hM : 0 < M) (j : Fin n → Fin M) :
    (Real.sqrt ((gridSpacing M)^n)*∏ i, Real.sqrt (phi (section5_grid_node n M j i)))^2 =
      ((gridSpacing M)^n*(Real.sqrt (2*Real.pi))⁻¹^n)*
        Real.exp (-‖(WithLp.toLp 2 (section5_grid_node n M j) : EuclideanSpace ℝ (Fin n))‖^2/2) := by
  rw [mul_pow,Real.sq_sqrt (pow_nonneg (section5_gridSpacing_positive M hM).le n),
    ← Finset.prod_pow]
  simp_rw [Real.sq_sqrt (phi_pos _).le]
  change (gridSpacing M)^n * section5_gaussian_density n (section5_grid_node n M j) = _
  rw [section5_gaussian_density_exp]
  ring

theorem section5_finite_phase_state_apply {n : ℕ} (w : EuclideanSpace ℝ (Fin n))
    (M : ℕ) (hM : 0 < M) (j : Fin n → Fin M) :
    section5_finite_phase_state w M j =
      section5_ltf_phase w (section5_grid_node n M j)*
        (Real.sqrt
          (Real.exp (-‖(WithLp.toLp 2 (section5_grid_node n M j) : EuclideanSpace ℝ (Fin n))‖^2/2)/
            ∑ k : Fin n → Fin M,
              Real.exp (-‖(WithLp.toLp 2 (section5_grid_node n M k) : EuclideanSpace ℝ (Fin n))‖^2/2)) : ℂ) := by
  rw [section5_finite_phase_state,section5_grid_phase_as_positive_amplitudes]
  rw [section5_normalize_positive_amplitudes _ _
    (fun k => section5_ltf_phase_norm w _) (fun k => by positivity)]
  simp_rw [section5_grid_phase_amplitude_sq n M hM]
  rw [← Finset.mul_sum]
  have hc : (gridSpacing M)^n*(Real.sqrt (2*Real.pi))⁻¹^n ≠ 0 := by
    apply ne_of_gt
    exact mul_pos (pow_pos (section5_gridSpacing_positive M hM) n) (by positivity)
  rw [mul_div_mul_left _ _ hc]

theorem section5_bit_grid_node_eq {n q : ℕ} (hq : 0 < q) (z : Fin n → Qubits q) :
    (WithLp.toLp 2 (section5_grid_node n (2^q) (section5_bit_grid_equiv n q z)) :
      EuclideanSpace ℝ (Fin n)) = gridPoint (flatReg n q z) := by
  rw [section5_gridPoint_flatReg]
  ext i
  exact (section5_scalarGrid_grid_node hq (z i)).symm





end
namespace «Aux_w_53_hermite»
end «Aux_w_53_hermite»
set_option autoImplicit false
open MeasureTheory QAlgorithms QuantumLTF.Example QuantumLTF.Membership Aux_w_53_hermite
theorem solution {n q : ℕ} (w : EuclideanSpace ℝ (Fin n))
    (hq : 0 < q) (z : Fin n → Qubits q) :
    section5_bit_phase_state w q z =
      (ltf w 0 (gridPoint (flatReg n q z)) : ℂ)*section5_grid_amplitude (flatReg n q z) := by
  change section5_finite_phase_state w (2^q) (section5_bit_grid_equiv n q z) = _
  rw [section5_finite_phase_state_apply w (2^q) (Nat.two_pow_pos q),section5_grid_exp_sum hq]
  unfold section5_ltf_phase
  rw [section5_bit_grid_node_eq hq]
  rfl
