-- Prove2me | solution 1 for section5_fixed_width_matrix_power_circuit
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T20:27:25.681131+00:00
-- url     : https://prove2.me/submissions/b515fb35-949c-49ee-b0d2-265570f67b08

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
import Definitions.Def_QuantumLTF_Membership_flatReg
import Definitions.Def_QuantumLTF_Membership_fpVal
import Definitions.Def_QuantumLTF_Membership_gates12
import Definitions.Def_QuantumLTF_Membership_gatesRev
import Definitions.Def_QuantumLTF_Membership_splitReg
import Definitions.Def_Section5Verified_Section5MatrixPowerCircuit
import Definitions.Def_Section5Verified_Section5ModularMatrixPowers
import Definitions.Def_Section5Verified_Section5SequentialClassicalCompiler
import Mathlib
import Theorems.Thm_section5_classical_stages_compiled
import Theorems.Thm_section5_fixed_width_complex_matrix_circuit
section
set_option autoImplicit false

open QAlgorithms QuantumLTF.Membership Thm49Primitives

/-! A complete circuit for repeated matrix multiplication at a fixed precision.
Earlier matrix registers are retained as reversible workspace. -/



theorem section5_flatten_matrix_register_on {m n w : ℕ}
    (p : Fin (2*n*n) → Fin w ↪ Fin m) (i : Fin (2*n*n)) (j : Fin w) :
    section5_flatten_matrix_register p (finProdFinEquiv (i,j))=p i j := by
  simp [section5_flatten_matrix_register]



theorem section5_flat_matrix_read {m n w : ℕ}
    (p : Fin (2*n*n) → Fin w ↪ Fin m) (z : Qubits m) :
    section5_decode_flat_matrix (z ∘ section5_flatten_matrix_register p)=section5_mod_matrix_read p z := by
  unfold section5_decode_flat_matrix section5_mod_matrix_read
  congr 1
  funext i
  congr 1
  congr 1
  funext j
  simp [Function.comp_def,section5_flatten_matrix_register_on]

theorem section5_mod_matrix_one_mul {n w : ℕ} (A : Section5ModMatrix n w) :
    (Section5ModMatrix.one n w).mul A=A := by
  apply Section5ModMatrix.ext <;>
    simp [Section5ModMatrix.one,Section5ModMatrix.mul]

theorem section5_mod_matrix_iteration {n w : ℕ} (A : Section5ModMatrix n w) (K : ℕ) :
    section5_left_iteration Section5ModMatrix.mul A K=A.power (K+1) := by
  induction K with
  | zero => simp only [section5_left_iteration,Section5ModMatrix.power,section5_mod_matrix_one_mul]
  | succ k ih =>
    rw [section5_left_iteration,ih]
    rfl



end
set_option autoImplicit false
open QAlgorithms QuantumLTF.Membership Thm49Primitives
theorem solution {m n b K : ℕ}
    (p : Fin (K+1) → Fin (2*n*n) → Fin (b+1) ↪ Fin m)
    (anc : Fin (b+1+1) ↪ Fin m) (t : Fin m)
    (hcomponents : ∀ s i j, i ≠ j → ∀ e f, p s i e ≠ p s j f)
    (hstages : ∀ s v, s ≠ v → ∀ i j e f, p s i e ≠ p v j f)
    (hpa : ∀ s i e j, p s i e ≠ anc j) (hpt : ∀ s i e, p s i e ≠ t)
    (hta : ∀ j, t ≠ anc j) :
    ∃ circ : Circuit gatesRev m, circ.size ≤ (88*n^3*(b+1)^3)*K ∧
      ∀ z : Qubits m, z t=false → (∀ j, z (anc j)=false) →
        (∀ s : Fin (K+1), 0 < s.val → ∀ i e, z (p s i e)=false) →
        ∃ z' : Qubits m, act circ.unitary (ket z)=ket z' ∧
          section5_mod_matrix_read (p (Fin.last K)) z'=(section5_mod_matrix_read (p 0) z).power (K+1) ∧
          z' t=false ∧ (∀ j, z' (anc j)=false) ∧
          ∀ j, (∀ s : Fin K, ∀ i, j ∉ Set.range (p s.succ i)) → z' j=z j := by
  classical
  let aux : Fin (b+1+1+1) → Fin m := Fin.snoc (fun j => anc j) t
  let reg : Fin (K+1) → Fin ((2*n*n)*(b+1)) → Fin m :=
    fun s => section5_flatten_matrix_register (p s)
  have hregpair : ∀ s v, s ≠ v → ∀ e f, reg s e ≠ reg v f := by
    intro s v hsv e f
    exact hstages s v hsv _ _ _ _
  have haux : ∀ s j e, aux j ≠ reg s e := by
    intro s j e
    refine Fin.lastCases ?_ (fun k => ?_) j
    · simpa only [aux,Fin.snoc_last,reg,section5_flatten_matrix_register] using
        (hpt s (finProdFinEquiv.symm e).1 (finProdFinEquiv.symm e).2).symm
    · simpa only [aux,Fin.snoc_castSucc,reg,section5_flatten_matrix_register] using
        (hpa s (finProdFinEquiv.symm e).1 (finProdFinEquiv.symm e).2 k).symm
  have hsteps : ∀ s : Fin K, ∃ c : Circuit gatesRev m, c.size ≤ 88*n^3*(b+1)^3 ∧
      ∀ z : Qubits m, (∀ j, z (aux j)=false) → (∀ e, z (reg s.succ e)=false) →
        ∃ z' : Qubits m, act c.unitary (ket z)=ket z' ∧
          (∀ j, j ∉ Set.range (reg s.succ) → z' j=z j) ∧
          section5_decode_flat_matrix (z' ∘ reg s.succ)=
            (section5_decode_flat_matrix (z ∘ reg s.castSucc)).mul
              (section5_decode_flat_matrix (z ∘ reg 0)) := by
    intro s
    obtain ⟨c,hc,hact⟩ := section5_fixed_width_complex_matrix_circuit
      (p s.castSucc) (p 0) (p s.succ) anc t (hcomponents s.succ)
      (hstages s.castSucc s.succ (by intro h; have := congrArg Fin.val h; simp at this))
      (hstages 0 s.succ (by intro h; have := congrArg Fin.val h; simp at this))
      (hpa s.succ) (fun i h => by obtain ⟨e,he⟩ := h; exact hpt s.succ i e he)
      hta (hpt s.castSucc) (hpt 0)
    refine ⟨c,hc,?_⟩
    intro z hza hz0
    have hzt : z t=false := by simpa only [aux,Fin.snoc_last] using hza (Fin.last (b+1+1))
    have hzanc : ∀ j, z (anc j)=false := by
      intro j
      simpa only [aux,Fin.snoc_castSucc] using hza j.castSucc
    have hzout : ∀ i e, z (p s.succ i e)=false := by
      intro i e
      simpa only [reg,section5_flatten_matrix_register_on] using hz0 (finProdFinEquiv (i,e))
    obtain ⟨z',hz',hoff,hval⟩ := hact z hzt hzanc hzout
    refine ⟨z',hz',?_,?_⟩
    · intro j hj
      apply hoff
      intro i
      rintro ⟨e,he⟩
      apply hj
      exact ⟨finProdFinEquiv (i,e),by simpa only [reg,section5_flatten_matrix_register_on] using he⟩
    · simpa only [reg,section5_flat_matrix_read] using hval
  choose cs hsize hact using hsteps
  obtain ⟨circ,hcirc,hcircact⟩ := section5_classical_stages_compiled cs reg aux
    section5_decode_flat_matrix Section5ModMatrix.mul hsize hregpair haux hact
  refine ⟨circ,hcirc,?_⟩
  intro z hzt hza hz0
  have hzaux : ∀ j, z (aux j)=false := by
    intro j
    refine Fin.lastCases ?_ (fun k => ?_) j
    · simpa only [aux,Fin.snoc_last] using hzt
    · simpa only [aux,Fin.snoc_castSucc] using hza k
  have hzregs : ∀ s : Fin (K+1), 0 < s.val → ∀ e, z (reg s e)=false := by
    intro s hs e
    exact hz0 s hs _ _
  obtain ⟨z',hz',hval,hclean,hoff⟩ := hcircact z hzaux hzregs
  refine ⟨z',hz',?_,?_,?_,?_⟩
  · simpa only [reg,section5_flat_matrix_read,section5_mod_matrix_iteration] using hval
  · simpa only [aux,Fin.snoc_last] using hclean (Fin.last (b+1+1))
  · intro j
    simpa only [aux,Fin.snoc_castSucc] using hclean j.castSucc
  · intro j hj
    apply hoff
    intro s
    rintro ⟨e,he⟩
    exact hj s (finProdFinEquiv.symm e).1 ⟨(finProdFinEquiv.symm e).2,he⟩
