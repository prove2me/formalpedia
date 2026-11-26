-- Prove2me | solution 1 for section5_uniform_window_comparator
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T20:25:57.796449+00:00
-- url     : https://prove2.me/submissions/5aecddd0-d9d8-4e43-aa5c-5dd83a9d16e7

import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QAlgorithms_Defs_Circuit
import Definitions.Def_QAlgorithms_Defs_Classical
import Definitions.Def_QAlgorithms_Defs_Gates
import Definitions.Def_QuantumLTF_Example_HermiteModel
import Definitions.Def_QuantumLTF_Example_qex
import Definitions.Def_QuantumLTF_Membership_Supplement_band1D53
import Definitions.Def_QuantumLTF_Membership_Supplement_bandKet
import Definitions.Def_QuantumLTF_Membership_Supplement_bandWeight
import Definitions.Def_QuantumLTF_Membership_Supplement_bitonicTrace54
import Definitions.Def_QuantumLTF_Membership_Supplement_hermCoeff
import Definitions.Def_QuantumLTF_Membership_Supplement_lcgSym54ArithV2
import Definitions.Def_QuantumLTF_Membership_Supplement_projDist
import Definitions.Def_QuantumLTF_Membership_Supplement_symBand54
import Definitions.Def_QuantumLTF_Membership_Supplement_thm410_router_blocks
import Definitions.Def_QuantumLTF_Membership_Supplement_thm49_primitives
import Definitions.Def_QuantumLTF_Membership_disagree
import Definitions.Def_QuantumLTF_Membership_flatReg
import Definitions.Def_QuantumLTF_Membership_fpVal
import Definitions.Def_QuantumLTF_Membership_gates12
import Definitions.Def_QuantumLTF_Membership_gatesRev
import Definitions.Def_QuantumLTF_Membership_ltf
import Definitions.Def_QuantumLTF_Membership_readFp
import Definitions.Def_QuantumLTF_Membership_splitReg
import Definitions.Def_Section5Verified_Section5BoundedWindow
import Definitions.Def_Section5Verified_Section5QuantizedOrientation
import Definitions.Def_Section5Verified_Section5RealWindow
import Mathlib
import Theorems.Thm_section5_fixed_point_window_comparator
import Theorems.Thm_section5_large_grid_fits_window
import Theorems.Thm_section5_middle_window_scales
import Theorems.Thm_section5_window_precision_bounds
section
set_option autoImplicit false

open QAlgorithms QuantumLTF.Membership QuantumLTF.Example Thm49Primitives

/-! Register-level implementation of the public fixed-point/window comparison.
The oracle precision q occurs in wire addresses, not in the circuit size bound. -/





theorem section5_comparator_polynomial_bound (n a b : ℕ) (hb : b ≤ 2*n+33) :
    (16*(n+a+b+1)+6)*(n*(a+2)*(b+1)) ≤ 128*(n+a+34)^4 := by
  let N := n+a+34
  have hN : 1 ≤ N := by dsimp only [N]; omega
  have hn : n ≤ N := by dsimp only [N]; omega
  have ha : a+2 ≤ N := by dsimp only [N]; omega
  have hb' : b+1 ≤ 2*N := by dsimp only [N]; omega
  have hg : 16*(n+a+b+1)+6 ≤ 54*N := by dsimp only [N]; omega
  calc
    _ ≤ (54*N)*(N*N*(2*N)) := Nat.mul_le_mul hg (Nat.mul_le_mul (Nat.mul_le_mul hn ha) hb')
    _ = 108*N^4 := by ring
    _ ≤ 128*N^4 := by omega



end
set_option autoImplicit false
open QAlgorithms QuantumLTF.Membership QuantumLTF.Example Thm49Primitives
theorem solution {m n q a : ℕ}
    (hn : 1 ≤ n) (hgrid : (2:ℝ)^40*(n:ℝ)^2 ≤ (2:ℝ)^q) (f : ℕ)
    (ov : Fin n → (Fin (a+1) ↪ Fin m)) (ex : Fin (n*q) ↪ Fin m)
    (p : Fin (n+a+(2*section5_window_precision n+1)+1) ↪ Fin m)
    (anc : Fin ((n+a+(2*section5_window_precision n+1)+1)+1) ↪ Fin m)
    (hpa : ∀ i j, p i ≠ anc j) (t : Fin m)
    (htp : t ∉ Set.range p) (hta : ∀ j, t ≠ anc j)
    (hut : ∀ i j, ov i j ≠ t) (hxt : ∀ j, ex j ≠ t)
    (hup : ∀ i j, ov i j ∉ Set.range p) (hxp : ∀ j, ex j ∉ Set.range p)
    (hxa : ∀ j k, ex j ≠ anc k) :
    ∃ circ : Circuit gatesRev m, circ.size ≤ 128*(n+a+34)^4 ∧
      ∀ z : Qubits m, z t=false → (∀ j, z (anc j)=false) → (∀ i, z (p i)=false) →
        ∃ z' : Qubits m, act circ.unitary (ket z)=ket z' ∧
          (∀ j, j ∉ Set.range p → z' j=z j) ∧
          (ltf (WithLp.toLp 2 (fun i => readFp (ov i) f z)) 0
            (section5_bounded_window_vector q (gridPoint (z ∘ ex)))=1 ↔
              z' (p (Fin.last (n+a+(2*section5_window_precision n+1))))=false) := by
  have hfit : q/2-section5_window_precision n+((2*section5_window_precision n+1)+1) ≤ q-1 := by
    have hh := (section5_middle_window_scales q (section5_window_precision n)
      (section5_large_grid_fits_window n q hn hgrid)).1
    omega
  obtain ⟨circ,hcirc,hact⟩ := section5_fixed_point_window_comparator
    (q/2-section5_window_precision n) f hfit ov ex p anc hpa t htp hta hut hxt hup hxp hxa
  refine ⟨circ,hcirc.trans (section5_comparator_polynomial_bound n a _ ?_),hact⟩
  have hb := (section5_window_precision_bounds n hn).2.2
  omega
