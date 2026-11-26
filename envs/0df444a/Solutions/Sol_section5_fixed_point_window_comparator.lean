-- Prove2me | solution 1 for section5_fixed_point_window_comparator
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T20:22:50.336368+00:00
-- url     : https://prove2.me/submissions/19dd9539-0d7b-430b-bad0-1f174e858173

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
import Definitions.Def_Section5Verified_Section5RealWindow
import Definitions.Def_Section5Verified_Section5SignedDotCircuit
import Definitions.Def_Section5Verified_Section5TwosComplement
import Definitions.Def_Section5Verified_Section5WindowComparator
import Definitions.Def_Section5Verified_Section5WindowDotIdentity
import Mathlib
import Theorems.Thm_section5_offset_integer_comparator
import Theorems.Thm_section5_window_integer_dot_label
set_option autoImplicit false
open QAlgorithms QuantumLTF.Membership QuantumLTF.Example Thm49Primitives
theorem solution {m n q a b : ℕ}
    (s f : ℕ) (hfit : s+(b+1) ≤ q-1)
    (ov : Fin n → (Fin (a+1) ↪ Fin m)) (ex : Fin (n*q) ↪ Fin m)
    (p : Fin (n+a+b+1) ↪ Fin m) (anc : Fin ((n+a+b+1)+1) ↪ Fin m)
    (hpa : ∀ i j, p i ≠ anc j) (t : Fin m)
    (htp : t ∉ Set.range p) (hta : ∀ j, t ≠ anc j)
    (hut : ∀ i j, ov i j ≠ t) (hxt : ∀ j, ex j ≠ t)
    (hup : ∀ i j, ov i j ∉ Set.range p) (hxp : ∀ j, ex j ∉ Set.range p)
    (hxa : ∀ j k, ex j ≠ anc k) :
    ∃ circ : Circuit gatesRev m, circ.size ≤
        (16*(n+a+b+1)+6)*(n*(a+2)*(b+1)) ∧
      ∀ z : Qubits m, z t=false → (∀ j, z (anc j)=false) → (∀ i, z (p i)=false) →
        ∃ z' : Qubits m, act circ.unitary (ket z)=ket z' ∧
          (∀ j, j ∉ Set.range p → z' j=z j) ∧
          (ltf (WithLp.toLp 2 (fun i => readFp (ov i) f z)) 0
            (section5_real_window_vec ((2:ℤ)^s) ((2:ℤ)^b) (gridSpacing (2^q))
              (gridPoint (z ∘ ex)))=1 ↔ z' (p (Fin.last (n+a+b)))=false) := by
  let u := fun i : Fin n => fun j : Fin (a+1) => ov i j.rev
  let x := section5_window_read_wire ex s b hfit
  obtain ⟨circ,hcirc,hact⟩ := section5_offset_integer_comparator u x p anc hpa t htp hta
    (fun i j => hut i j.rev) (fun i j => hxt _)
    (fun i j => hup i j.rev) (fun i j => hxp _) (fun i j k => hxa _ k)
  refine ⟨circ,hcirc,?_⟩
  intro z hzt hzanc hz0
  obtain ⟨z',hz',hoff,hsign⟩ := hact z hzt hzanc hz0
  refine ⟨z',hz',hoff,?_⟩
  have hidentity := section5_window_integer_dot_label f (fun i => z ∘ ov i) (z ∘ ex) s b hfit
  change ltf (WithLp.toLp 2 (fun i => readFp (ov i) f z)) 0 _ = _ at hidentity
  rw [hidentity]
  change (sgn (_:ℝ)=1 ↔ _)
  have hD : (0 ≤ section5_window_integer_dot (fun i => z ∘ ov i) (z ∘ ex) s b hfit) ↔
      z' (p (Fin.last (n+a+b)))=false := by
    exact hsign
  rw [← hD]
  unfold sgn
  have hcast : (0:ℝ) ≤ (section5_window_integer_dot (fun i => z ∘ ov i) (z ∘ ex) s b hfit:ℤ) ↔
      0 ≤ section5_window_integer_dot (fun i => z ∘ ov i) (z ∘ ex) s b hfit := by norm_cast
  simp only [hcast]
  split_ifs <;> simp_all
