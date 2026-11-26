-- Prove2me | solution 1 for section5_tensor_grid_vector_bits
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T20:00:28.485352+00:00
-- url     : https://prove2.me/submissions/dfd59abb-aa51-441e-9288-a3e538282a8c

import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QuantumLTF_Example_HermiteModel
import Definitions.Def_QuantumLTF_Membership_Supplement_band1D53
import Definitions.Def_QuantumLTF_Membership_Supplement_bandKet
import Definitions.Def_QuantumLTF_Membership_Supplement_bandWeight
import Definitions.Def_QuantumLTF_Membership_Supplement_hermCoeff
import Definitions.Def_QuantumLTF_Membership_Supplement_projDist
import Definitions.Def_QuantumLTF_Membership_flatReg
import Definitions.Def_QuantumLTF_Membership_splitReg
import Definitions.Def_Section5Verified_Section5GridIsometry
import Definitions.Def_Section5Verified_Section5HermiteFoundations
import Definitions.Def_Section5Verified_Section5HermiteWavefunctions
import Definitions.Def_Section5Verified_Section5MultivariateSampling
import Definitions.Def_Section5Verified_Section5PhysicalHermiteGrid
import Definitions.Def_Section5Verified_Section5ProductSampling
import Mathlib
section
set_option autoImplicit false

namespace Aux_w_53_hermite

open MeasureTheory Filter Polynomial QAlgorithms QuantumLTF.Membership QuantumLTF.Membership.Supplement
open scoped Real Topology Nat ENNReal

/-! ### Part 1: 1D Gaussian Density, Orthonormal Hermite Functions, and `sgn` Coefficients -/





























lemma h1D_eq_div (j : ℕ) (x : ℝ) :
    h1D j x = Polynomial.aeval x (Polynomial.hermite j) / Real.sqrt (j.factorial) := by
  simp [h1D, Hpoly, div_eq_inv_mul]























































/-! ### Part 2: Multivariate Hermite Orthonormality & Orthogonal-Projection Invariance -/





























end Aux_w_53_hermite


end
section
set_option autoImplicit false

open MeasureTheory QAlgorithms QuantumLTF.Example Aux_w_53_hermite

/-! Matching the exact physical Hermite grid normalization and bit convention. -/

theorem section5_grid_gaussian_factor (M : ℕ) (hM : 0 < M) (x : ℝ) :
    gridSpacing M * phi x = Real.sqrt (2/M)*Real.exp (-(x^2/2)) := by
  have hM' : (0:ℝ) < M := by exact_mod_cast hM
  have hδ : 0 < gridSpacing M := section5_gridSpacing_positive M hM
  have hp : 0 < Real.sqrt (2*Real.pi) := Real.sqrt_pos.mpr (by positivity)
  have hc : gridSpacing M = Real.sqrt (2/M)*Real.sqrt (2*Real.pi) := by
    apply (mul_self_inj_of_nonneg hδ.le (by positivity)).mp
    rw [← sq,← sq,mul_pow,Real.sq_sqrt (by positivity : (0:ℝ) ≤ 2/M),
      Real.sq_sqrt (by positivity : (0:ℝ) ≤ 2*Real.pi)]
    unfold gridSpacing
    rw [Real.sq_sqrt (by positivity : (0:ℝ) ≤ 4*Real.pi/M)]
    ring
  rw [phi_def,hc]
  field_simp

theorem section5_grid_wave_scale (M : ℕ) (hM : 0 < M) (k : ℕ) (x : ℝ) :
    Real.sqrt (gridSpacing M)*section5_hermite_wave k x =
      ((2:ℝ)/M)^(1/4:ℝ)*Real.exp (-x^2/4)*h1D k x := by
  have hM' : (0:ℝ) < M := by exact_mod_cast hM
  have hfourth : (((2:ℝ)/M)^(1/4:ℝ))^2 = Real.sqrt (2/M) := by
    rw [← Real.rpow_natCast,← Real.rpow_mul (by positivity : (0:ℝ) ≤ 2/M)]
    convert (Real.sqrt_eq_rpow ((2:ℝ)/M)).symm using 1 <;> norm_num
  have hexp : (Real.exp (-x^2/4))^2 = Real.exp (-(x^2/2)) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have ha : Real.sqrt (gridSpacing M)*Real.sqrt (phi x) =
      ((2:ℝ)/M)^(1/4:ℝ)*Real.exp (-x^2/4) := by
    apply (mul_self_inj_of_nonneg (by positivity) (by positivity)).mp
    rw [← sq,← sq,mul_pow,mul_pow,
      Real.sq_sqrt (section5_gridSpacing_positive M hM).le,
      Real.sq_sqrt (phi_pos x).le,hfourth,hexp,section5_grid_gaussian_factor M hM x]
  unfold section5_hermite_wave
  rw [← mul_assoc,ha]

theorem section5_hermiteFn_eq_h1D (k : ℕ) (x : ℝ) : hermiteFn k x = h1D k x := by
  rw [hermiteFn,h1D_eq_div]
  congr 1
  simp only [Polynomial.aeval_def,Polynomial.eval_map]
  rw [show Int.castRingHom ℝ = algebraMap ℤ ℝ from Subsingleton.elim _ _]

theorem section5_discreteHermiteKet_grid_scale (q k : ℕ) (z : Qubits q) :
    discreteHermiteKet q k z =
      (Real.sqrt (gridSpacing (2^q))*section5_hermite_wave k (scalarGrid z) : ℝ) := by
  rw [section5_grid_wave_scale (2^q) (Nat.two_pow_pos q),← section5_hermiteFn_eq_h1D]
  simp only [discreteHermiteKet,Nat.cast_pow,Nat.cast_ofNat]

theorem section5_scalarGrid_grid_node {q : ℕ} (hq : 0 < q) (z : Qubits q) :
    scalarGrid z = -gridRadius (2^q)+(bitsEquivFin q z : ℝ)*gridSpacing (2^q) := by
  rcases q with _ | q
  · omega
  simp only [scalarGrid,gridRadius,gridSpacing,bitsEquivFin_apply,QuantumLTF.Example.bitsValue,
    bitsToNat,Nat.add_sub_cancel,pow_succ,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]
  ring













end
set_option autoImplicit false
open MeasureTheory QAlgorithms QuantumLTF.Example Aux_w_53_hermite
theorem solution (n q D : ℕ) (hq : 0 < q) (a : Fin n → Fin D) :
    section5_grid_bit_isometry n q
      (section5_grid_vector n (2^q) (section5_tensor_family (section5_complex_wave D) n a)) =
      section5_discrete_hermite_tensor n q D a := by
  ext z
  change (Real.sqrt ((gridSpacing (2^q))^n) : ℂ)*
    (∏ i, (section5_hermite_wave (a i)
      (-gridRadius (2^q)+(bitsEquivFin q (z i) : ℝ)*gridSpacing (2^q)) : ℂ)) =
      ∏ i, discreteHermiteKet q (a i) (z i)
  simp_rw [section5_discreteHermiteKet_grid_scale,section5_scalarGrid_grid_node hq]
  have hroot : Real.sqrt ((gridSpacing (2^q))^n) = (Real.sqrt (gridSpacing (2^q)))^n := by
    apply (mul_self_inj_of_nonneg (Real.sqrt_nonneg _) (by positivity)).mp
    rw [← sq,← sq,Real.sq_sqrt
        (pow_nonneg (section5_gridSpacing_positive (2^q) (Nat.two_pow_pos q)).le n),
      ← pow_mul, mul_comm n 2,pow_mul,
      Real.sq_sqrt (section5_gridSpacing_positive (2^q) (Nat.two_pow_pos q)).le]
  rw [hroot,Complex.ofReal_pow]
  simp_rw [Complex.ofReal_mul]
  rw [Finset.prod_mul_distrib,Finset.prod_const]
  simp only [Finset.card_univ,Fintype.card_fin]
