-- Prove2me | solution 1 for section5_elementary_qft
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T19:49:06.746831+00:00
-- url     : https://prove2.me/submissions/339d7764-e9cb-47ab-8b0d-146069ae8343

import Definitions.Def_QAlgorithms_Defs_Fourier
import Definitions.Def_QuantumLTF_Example_HermiteModel
import Definitions.Def_QuantumLTF_Membership_Supplement_thm49_primitives
import Definitions.Def_QuantumLTF_Membership_gates12
import Definitions.Def_Section5Verified_Section5FourierCircuit
import Definitions.Def_Section5Verified_Section5QFTFoundation
import Definitions.Def_Section5Verified_Section5QuadraticPhase
import Mathlib
import Theorems.Thm_SolQFTCircuitExact_embedOp_diagonal
import Theorems.Thm_SolQFTCircuitExact_qftQubits_step
section
set_option autoImplicit false

open QAlgorithms QuantumLTF.Membership Thm49Primitives

/-! Exact Fourier transforms in the mission's elementary gate set, reusing the
accepted QFT construction, and the centered Fourier convention for the QHO. -/

theorem section5_rotR_unitary (s : ℕ) : rotR s ∈ Matrix.unitaryGroup Bool ℂ := by
  apply Matrix.mem_unitaryGroup_iff.mpr
  rw [rotR]
  change _ * (Matrix.diagonal _).conjTranspose=1
  rw [Matrix.diagonal_conjTranspose,Matrix.diagonal_mul_diagonal]
  ext a b
  by_cases hab : a=b
  · subst b
    simp only [Matrix.diagonal_apply_eq,Matrix.one_apply_eq,Pi.star_apply]
    cases a
    · simp
    · have h := section5_phase_star (2*Real.pi/(2:ℝ)^s)
      simpa [section5_phase,Complex.ofReal_div,Complex.ofReal_mul,Complex.ofReal_pow,
        Complex.ofReal_ofNat,mul_div_assoc,mul_comm,mul_left_comm,mul_assoc] using h
  · simp [hab]

theorem section5_qft_gates_elementary : qftGateSet ⊆ gates12 := by
  intro g hg
  simp only [qftGateSet,Set.mem_union,Set.mem_singleton_iff,Set.mem_setOf_eq] at hg
  rcases hg with (rfl | ⟨s,hs,rfl⟩) | rfl
  · exact ofMatrix1_mem_gates12 hadamard_mem_unitaryGroup
  · exact ofMatrix2_mem_gates12 (controlled_mem_unitaryGroup (section5_rotR_unitary s))
  · exact ofMatrix2_mem_gates12 swapGate_mem_unitaryGroup



theorem section5_change_gate_set_size {S T : Set Gate} (h : S ⊆ T) {n : ℕ}
    (c : Circuit S n) : (section5_change_gate_set h c).size=c.size := by
  simp [section5_change_gate_set,Circuit.size]

theorem section5_change_gate_set_unitary {S T : Set Gate} (h : S ⊆ T) {n : ℕ}
    (c : Circuit S n) : (section5_change_gate_set h c).unitary=c.unitary := by
  simp [section5_change_gate_set,Circuit.unitary,List.map_map,Function.comp_def]









end
section
set_option autoImplicit false

open QAlgorithms
open scoped Matrix BigOperators

namespace SolQFTCircuitExact





@[simp]
lemma init_snoc_qubits {n : ℕ} (u : Qubits n) (b : Bool) :
    Fin.init (Fin.snoc u b : Qubits (n + 1)) = u := by
  simp

@[simp]
lemma snoc_last_qubits {n : ℕ} (u : Qubits n) (b : Bool) :
    (Fin.snoc u b : Qubits (n + 1)) (Fin.last n) = b := by
  simp

@[simp]
lemma snoc_castSucc_qubits {n : ℕ} (u : Qubits n) (b : Bool) (i : Fin n) :
    (Fin.snoc u b : Qubits (n + 1)) (Fin.castSucc i) = u i := by
  simp





@[simp]
lemma liftCircuit_size {S : Set Gate} {n : ℕ} (c : Circuit S n) :
    Circuit.size (liftCircuit c) = Circuit.size c := by
  simp [Circuit.size, liftCircuit]



@[simp]
lemma liftInit_apply {n : ℕ} (A : Matrix (Qubits n) (Qubits n) ℂ) (y z : Qubits (n + 1)) :
    liftInit A y z = if y (Fin.last n) = z (Fin.last n) then A (Fin.init y) (Fin.init z) else 0 :=
  rfl

lemma eq_iff_init_eq_and_last_eq {n : ℕ} (y z : Qubits (n + 1)) :
    y = z ↔ Fin.init y = Fin.init z ∧ y (Fin.last n) = z (Fin.last n) := by
  constructor
  · rintro rfl; exact ⟨rfl, rfl⟩
  · rintro ⟨h1, h2⟩
    funext i
    refine Fin.lastCases h2 (fun j => ?_) i
    exact congrFun h1 j

lemma liftInit_one (n : ℕ) : liftInit (1 : Matrix (Qubits n) (Qubits n) ℂ) = 1 := by
  ext y z
  simp only [liftInit_apply, Matrix.one_apply]
  by_cases hlast : y (Fin.last n) = z (Fin.last n)
  · rw [if_pos hlast]
    by_cases hinit : Fin.init y = Fin.init z
    · have hyz : y = z := (eq_iff_init_eq_and_last_eq y z).2 ⟨hinit, hlast⟩
      simp [hyz]
    · have hyz : y ≠ z := fun h => hinit (congrArg Fin.init h)
      simp [hinit, hyz]
  · have hyz : y ≠ z := fun h => hlast (congrFun h (Fin.last n))
    simp [hlast, hyz]

lemma liftInit_mul {n : ℕ} (A B : Matrix (Qubits n) (Qubits n) ℂ) :
    liftInit (A * B) = liftInit A * liftInit B := by
  ext y z
  simp only [liftInit_apply, Matrix.mul_apply]
  let e : Qubits n × Bool ≃ Qubits (n + 1) :=
    { toFun := fun p => Fin.snoc p.1 p.2
      invFun := fun x => (Fin.init x, x (Fin.last n))
      left_inv := fun p => by ext <;> simp
      right_inv := fun x => Fin.snoc_init_self x }
  rw [← Equiv.sum_comp e]
  simp only [e, Equiv.coe_fn_mk, init_snoc_qubits, snoc_last_qubits, Fintype.sum_prod_type]
  by_cases hlast : y (Fin.last n) = z (Fin.last n)
  · rw [if_pos hlast]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Fintype.sum_eq_single (y (Fin.last n))]
    · simp [hlast]
    · intro b hb
      rw [if_neg (Ne.symm hb), zero_mul]
  · rw [if_neg hlast]
    symm
    refine Finset.sum_eq_zero fun x _ => ?_
    refine Finset.sum_eq_zero fun b _ => ?_
    by_cases hb : y (Fin.last n) = b
    · subst hb
      rw [if_neg hlast, mul_zero]
    · rw [if_neg hb, zero_mul]

lemma embedOp_trans_castSuccEmb {k n : ℕ} (M : Matrix (Qubits k) (Qubits k) ℂ)
    (w : Fin k ↪ Fin n) :
    embedOp M (w.trans Fin.castSuccEmb) = liftInit (embedOp M w) := by
  ext y z
  simp only [embedOp, liftInit_apply, Matrix.of_apply]
  have hcomp : ∀ x : Qubits (n + 1), x ∘ w.trans Fin.castSuccEmb = Fin.init x ∘ w := by
    intro x; funext i; rfl
  rw [hcomp y, hcomp z]
  have hcond : (∀ a : Fin (n + 1), a ∉ Set.range (w.trans Fin.castSuccEmb) → y a = z a) ↔
      y (Fin.last n) = z (Fin.last n) ∧ ∀ a : Fin n, a ∉ Set.range w → Fin.init y a = Fin.init z a := by
    constructor
    · intro h
      refine ⟨h (Fin.last n) ?_, fun a ha => h (Fin.castSucc a) ?_⟩
      · rintro ⟨i, hi⟩
        exact Fin.castSucc_ne_last (w i) hi
      · rintro ⟨i, hi⟩
        exact ha ⟨i, Fin.castSucc_inj.1 hi⟩
    · rintro ⟨hlast, hinit⟩ a
      refine Fin.lastCases (fun _ => hlast) (fun j ha => hinit j ?_) a
      rintro ⟨i, rfl⟩
      exact ha ⟨i, rfl⟩
  by_cases hlast : y (Fin.last n) = z (Fin.last n)
  · rw [if_pos hlast]
    by_cases hinit : ∀ a : Fin n, a ∉ Set.range w → Fin.init y a = Fin.init z a
    · rw [if_pos (hcond.2 ⟨hlast, hinit⟩), if_pos hinit]
    · rw [if_neg (fun h => hinit (hcond.1 h).2), if_neg hinit]
  · rw [if_neg hlast, if_neg (fun h => hlast (hcond.1 h).1)]

lemma liftInit_list_prod {n : ℕ} (L : List (Matrix (Qubits n) (Qubits n) ℂ)) :
    (L.map liftInit).prod = liftInit L.prod := by
  induction L with
  | nil => simp [liftInit_one]
  | cons A L ih => simp [List.prod_cons, ih, liftInit_mul]

lemma liftCircuit_unitary {S : Set Gate} {n : ℕ} (c : Circuit S n) :
    Circuit.unitary (liftCircuit c) = liftInit (Circuit.unitary c) := by
  simp only [Circuit.unitary, liftCircuit, ← List.map_reverse]
  rw [List.map_map]
  have hmap : ((fun g => embedOp g.gate.mat g.wires) ∘ liftGateApp) =
      liftInit ∘ (fun g : GateApp S n => embedOp g.gate.mat g.wires) := by
    funext g
    simp [liftGateApp, embedOp_trans_castSuccEmb]
  rw [hmap, ← List.map_map, liftInit_list_prod]

lemma circuit_unitary_append {S : Set Gate} {n : ℕ} (c1 c2 : Circuit S n) :
    Circuit.unitary (c1 ++ c2) = Circuit.unitary c2 * Circuit.unitary c1 := by
  simp [Circuit.unitary, List.map_append, List.reverse_append, List.prod_append]

lemma circuit_size_append {S : Set Gate} {n : ℕ} (c1 c2 : Circuit S n) :
    Circuit.size (c1 ++ c2) = Circuit.size c1 + Circuit.size c2 := by
  simp [Circuit.size]





lemma embedOp_ctrlRotApp {n : ℕ} (s : ℕ) (hs : 1 ≤ s) (c t : Fin n) (hct : c ≠ t) :
    embedOp (ctrlRotApp s hs c t hct).gate.mat (ctrlRotApp s hs c t hct).wires =
      Matrix.diagonal (fun y : Qubits n =>
        if y c && y t then Complex.exp (2 * Real.pi * Complex.I / (2 : ℂ) ^ s) else 1) := by
  change embedOp ((controlled (rotR s)).submatrix (fun b : Qubits 2 => (b 0, b 1))
    (fun b : Qubits 2 => (b 0, b 1))) (wire2 c t hct) = _
  have hmat : (controlled (rotR s)).submatrix (fun b : Qubits 2 => (b 0, b 1))
      (fun b : Qubits 2 => (b 0, b 1)) =
      Matrix.diagonal (fun b : Qubits 2 =>
        if b 0 && b 1 then Complex.exp (2 * Real.pi * Complex.I / (2 : ℂ) ^ s) else 1) := by
    ext y z
    simp only [Matrix.submatrix_apply, controlled, rotR, Matrix.of_apply,
      Matrix.diagonal_apply, Matrix.one_apply]
    by_cases hyz : y = z
    · subst hyz
      cases y 0 <;> cases y 1 <;> simp
    · rw [if_neg hyz]
      by_cases h0 : y 0 = z 0
      · have h1 : y 1 ≠ z 1 := by
          intro h1
          apply hyz
          funext i
          fin_cases i
          · exact h0
          · exact h1
        simp [h0, h1]
      · simp [h0]
  rw [hmat, embedOp_diagonal]
  rfl



@[simp]
lemma phaseCircuit_size (n : ℕ) : Circuit.size (phaseCircuit n) = n := by
  simp [Circuit.size, phaseCircuit]

lemma list_prod_diagonal {ι : Type*} [Fintype ι] [DecidableEq ι] {α : Type*}
    (L : List α) (f : α → ι → ℂ) :
    (L.map (fun a => Matrix.diagonal (f a))).prod =
      Matrix.diagonal (fun y => (L.map (fun a => f a y)).prod) := by
  induction L with
  | nil =>
      ext y z
      by_cases h : y = z <;> simp [Matrix.diagonal, h]
  | cons a L ih =>
      rw [List.map_cons, List.prod_cons, ih, Matrix.diagonal_mul_diagonal]
      rfl

lemma phaseCircuit_unitary (n : ℕ) :
    Circuit.unitary (phaseCircuit n) =
      Matrix.diagonal (fun y : Qubits (n + 1) =>
        ∏ m : Fin n,
          if y (Fin.castSucc m) && y (Fin.last n) then
            Complex.exp (2 * Real.pi * Complex.I / (2 : ℂ) ^ ((m : ℕ) + 2))
          else 1) := by
  simp only [Circuit.unitary, phaseCircuit, List.map_ofFn]
  let f : Fin n → Qubits (n + 1) → ℂ := fun m y =>
    if y (Fin.castSucc m) && y (Fin.last n) then
      Complex.exp (2 * Real.pi * Complex.I / (2 : ℂ) ^ ((m : ℕ) + 2))
    else 1
  have hfun : (fun g => embedOp g.gate.mat g.wires) ∘
      (fun m : Fin n => ctrlRotApp ((m : ℕ) + 2) (by omega) (Fin.castSucc m) (Fin.last n)
        (Fin.castSucc_ne_last m)) =
      fun m : Fin n => Matrix.diagonal (f m) := by
    funext m
    exact embedOp_ctrlRotApp ((m : ℕ) + 2) (by omega) (Fin.castSucc m) (Fin.last n)
      (Fin.castSucc_ne_last m)
  rw [hfun]
  have hofFn : List.ofFn (fun m : Fin n => Matrix.diagonal (f m)) =
      (List.finRange n).map (fun m : Fin n => Matrix.diagonal (f m)) := by
    rw [List.ofFn_eq_map]
  rw [hofFn, ← List.map_reverse, list_prod_diagonal]
  congr 1
  funext y
  rw [List.map_reverse, List.prod_reverse, ← List.ofFn_eq_map, Fin.prod_ofFn]



lemma embedOp_hadApp_last (n : ℕ) (y z : Qubits (n + 1)) :
    embedOp (hadApp (Fin.last n)).gate.mat (hadApp (Fin.last n)).wires y z =
      if Fin.init y = Fin.init z then hadamard (y (Fin.last n)) (z (Fin.last n)) else 0 := by
  change embedOp (hadamard.submatrix (fun b : Qubits 1 => b 0) (fun b : Qubits 1 => b 0))
    (wire1 (Fin.last n)) y z = _
  simp only [embedOp, Matrix.of_apply, Matrix.submatrix_apply]
  have hcond : (∀ a : Fin (n + 1), a ∉ Set.range (wire1 (Fin.last n)) → y a = z a) ↔
      Fin.init y = Fin.init z := by
    constructor
    · intro h
      funext j
      refine h (Fin.castSucc j) ?_
      rintro ⟨i, hi⟩
      exact Fin.castSucc_ne_last j hi.symm
    · intro h a
      refine Fin.lastCases (fun ha => absurd ⟨0, rfl⟩ ha) (fun j _ => congrFun h j) a
  by_cases hinit : Fin.init y = Fin.init z
  · rw [if_pos (hcond.2 hinit), if_pos hinit]
    rfl
  · rw [if_neg (fun h => hinit (hcond.1 h)), if_neg hinit]



lemma embedOp_swapApp {n : ℕ} (c t : Fin n) (hct : c ≠ t) (y z : Qubits n) :
    embedOp (swapApp c t hct).gate.mat (swapApp c t hct).wires y z =
      if y ∘ Equiv.swap c t = z then 1 else 0 := by
  change embedOp (swapGate.submatrix (fun b : Qubits 2 => (b 0, b 1))
    (fun b : Qubits 2 => (b 0, b 1))) (wire2 c t hct) y z = _
  simp only [embedOp, swapGate, Matrix.of_apply, Matrix.submatrix_apply]
  have h0 : wire2 c t hct 0 = c := rfl
  have h1 : wire2 c t hct 1 = t := rfl
  simp only [Function.comp_apply, h0, h1]
  by_cases hswap : y ∘ Equiv.swap c t = z
  · subst hswap
    have hcond : ∀ a : Fin n, a ∉ Set.range (wire2 c t hct) →
        y a = (y ∘ Equiv.swap c t) a := by
      intro a ha
      have hac : a ≠ c := fun h => ha ⟨0, h.symm⟩
      have hat : a ≠ t := fun h => ha ⟨1, h.symm⟩
      simp only [Function.comp_apply, Equiv.swap_apply_of_ne_of_ne hac hat]
    rw [if_pos hcond]
    simp [Equiv.swap_apply_left, Equiv.swap_apply_right]
  · rw [if_neg hswap]
    split_ifs with hcond hpair
    · exfalso
      apply hswap
      funext a
      by_cases hac : a = c
      · subst hac
        simpa [Equiv.swap_apply_left] using (Prod.mk.inj hpair).2
      · by_cases hat : a = t
        · subst hat
          simpa [Equiv.swap_apply_right] using (Prod.mk.inj hpair).1
        · have ha : a ∉ Set.range (wire2 c t hct) := by
            rintro ⟨i, hi⟩
            fin_cases i
            · exact hac hi.symm
            · exact hat hi.symm
          simp only [Function.comp_apply, Equiv.swap_apply_of_ne_of_ne hac hat]
          exact hcond a ha
    · rfl
    · rfl

lemma embedOp_swapApp_mul {n : ℕ} (c t : Fin n) (hct : c ≠ t)
    (A : Matrix (Qubits n) (Qubits n) ℂ) (y k : Qubits n) :
    (embedOp (swapApp c t hct).gate.mat (swapApp c t hct).wires * A) y k =
      A (y ∘ Equiv.swap c t) k := by
  rw [Matrix.mul_apply]
  rw [Fintype.sum_eq_single (y ∘ Equiv.swap c t)]
  · rw [embedOp_swapApp, if_pos rfl, one_mul]
  · intro z hz
    rw [embedOp_swapApp, if_neg hz.symm, zero_mul]



@[simp]
lemma cycleSwaps_size (n : ℕ) : Circuit.size (cycleSwaps n) = n := by
  induction n with
  | zero => rfl
  | succ m ih =>
      rw [cycleSwaps, circuit_size_append, liftCircuit_size, ih]
      simp [Circuit.size]
      omega

lemma snoc_snoc_comp_swap {m : ℕ} (y : Qubits (m + 2)) :
    Fin.snoc (Fin.snoc (Fin.tail (Fin.init y)) (Fin.init y 0)) (y (Fin.last (m + 1))) ∘
      Equiv.swap (Fin.castSucc (Fin.last m)) (Fin.last (m + 1)) =
      Fin.snoc (Fin.tail y) (y 0) := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [Equiv.swap_apply_right, Fin.snoc_castSucc, Fin.snoc_last, Fin.init]
  · refine Fin.lastCases ?_ (fun j0 => ?_) j
    · simp [Equiv.swap_apply_left, Fin.snoc_last, Fin.snoc_castSucc, Fin.tail]
    · have hne1 : Fin.castSucc (Fin.castSucc j0) ≠ Fin.castSucc (Fin.last m) := by
        intro h
        exact Fin.castSucc_ne_last j0 (Fin.castSucc_inj.1 h)
      have hne2 : Fin.castSucc (Fin.castSucc j0) ≠ Fin.last (m + 1) :=
        Fin.castSucc_ne_last _
      rw [Function.comp_apply, Equiv.swap_apply_of_ne_of_ne hne1 hne2]
      simp only [Fin.snoc_castSucc, Fin.tail, Fin.init]
      rfl

lemma cycleSwaps_unitary_mul (n : ℕ) (A : Matrix (Qubits (n + 1)) (Qubits (n + 1)) ℂ)
    (y k : Qubits (n + 1)) :
    (Circuit.unitary (cycleSwaps n) * A) y k = A (Fin.snoc (Fin.tail y) (y 0)) k := by
  induction n with
  | zero =>
      have hy : Fin.snoc (Fin.tail y) (y 0) = y := by
        funext i
        fin_cases i
        rfl
      simp [cycleSwaps, Circuit.unitary, hy]
  | succ m ih =>
      rw [cycleSwaps, circuit_unitary_append, liftCircuit_unitary, Matrix.mul_assoc]
      have hsingle : Circuit.unitary
          [swapApp (Fin.castSucc (Fin.last m)) (Fin.last (m + 1)) (Fin.castSucc_ne_last _)] =
          embedOp (swapApp (Fin.castSucc (Fin.last m)) (Fin.last (m + 1))
            (Fin.castSucc_ne_last _)).gate.mat
            (swapApp (Fin.castSucc (Fin.last m)) (Fin.last (m + 1))
              (Fin.castSucc_ne_last _)).wires := by
        simp [Circuit.unitary]
      rw [hsingle]
      let B := embedOp (swapApp (Fin.castSucc (Fin.last m)) (Fin.last (m + 1))
        (Fin.castSucc_ne_last _)).gate.mat
        (swapApp (Fin.castSucc (Fin.last m)) (Fin.last (m + 1)) (Fin.castSucc_ne_last _)).wires * A
      let C : Matrix (Qubits (m + 1)) (Qubits (m + 1)) ℂ :=
        Matrix.of fun u _ => B (Fin.snoc u (y (Fin.last (m + 1)))) k
      have hBC : (liftInit (Circuit.unitary (cycleSwaps m)) * B) y k =
          (Circuit.unitary (cycleSwaps m) * C) (Fin.init y) (Fin.init y) := by
        simp only [Matrix.mul_apply, liftInit_apply, C, Matrix.of_apply]
        let e : Qubits (m + 1) × Bool ≃ Qubits (m + 2) :=
          { toFun := fun p => Fin.snoc p.1 p.2
            invFun := fun x => (Fin.init x, x (Fin.last (m + 1)))
            left_inv := fun p => by ext <;> simp
            right_inv := fun x => Fin.snoc_init_self x }
        rw [← Equiv.sum_comp e]
        simp only [e, Equiv.coe_fn_mk, init_snoc_qubits, snoc_last_qubits, Fintype.sum_prod_type]
        refine Finset.sum_congr rfl fun u _ => ?_
        rw [Fintype.sum_eq_single (y (Fin.last (m + 1)))]
        · simp
        · intro b hb
          rw [if_neg (Ne.symm hb), zero_mul]
      rw [hBC, ih C (Fin.init y) (Fin.init y)]
      simp only [C, Matrix.of_apply, B]
      rw [embedOp_swapApp_mul, snoc_snoc_comp_swap]











lemma qftQubits_apply (n : ℕ) (j k : Qubits n) :
    qftQubits n j k =
      Complex.exp (2 * Real.pi * Complex.I * ((bitsToNat j : ℂ) * (bitsToNat k : ℂ)) /
        (2 ^ n : ℂ)) / (Real.sqrt (2 ^ n) : ℂ) := by
  simp [qftQubits, qftMatrix, bitsEquivFin_apply]





lemma qftCircuit_size (n : ℕ) : Circuit.size (qftCircuit n) ≤ n ^ 2 := by
  induction n with
  | zero => simp [qftCircuit, Circuit.size]
  | succ n ih =>
      rw [qftCircuit, circuit_size_append, circuit_size_append, circuit_size_append,
        liftCircuit_size, phaseCircuit_size, cycleSwaps_size]
      have hhad : Circuit.size ([hadApp (Fin.last n)] : Circuit qftGateSet (n + 1)) = 1 := rfl
      rw [hhad]
      nlinarith

lemma diagonal_mul_apply {ι : Type*} [Fintype ι] [DecidableEq ι]
    (d : ι → ℂ) (M : Matrix ι ι ℂ) (i j : ι) :
    (Matrix.diagonal d * M) i j = d i * M i j := by
  simp [Matrix.mul_apply, Matrix.diagonal]

lemma qftCircuit_unitary (n : ℕ) : Circuit.unitary (qftCircuit n) = qftQubits n := by
  induction n with
  | zero =>
      ext j k
      have hj : j = k := Subsingleton.elim j k
      subst hj
      simp [qftCircuit, Circuit.unitary, qftQubits_apply, bitsToNat]
  | succ n ih =>
      rw [qftCircuit, circuit_unitary_append, circuit_unitary_append, circuit_unitary_append,
        liftCircuit_unitary, ih]
      ext j k
      rw [cycleSwaps_unitary_mul]
      have hhad : Circuit.unitary ([hadApp (Fin.last n)] : Circuit qftGateSet (n + 1)) =
          embedOp (hadApp (Fin.last n)).gate.mat (hadApp (Fin.last n)).wires := by
        simp [Circuit.unitary]
      rw [hhad, phaseCircuit_unitary]
      let y0 : Qubits (n + 1) := Fin.snoc (Fin.tail j) (j 0)
      let z0 : Qubits (n + 1) := Fin.snoc (Fin.tail j) (k (Fin.last n))
      rw [Matrix.mul_apply]
      rw [Fintype.sum_eq_single z0]
      · dsimp only [z0]
        rw [embedOp_hadApp_last, init_snoc_qubits, init_snoc_qubits, if_pos rfl,
          snoc_last_qubits, snoc_last_qubits, diagonal_mul_apply, liftInit_apply,
          snoc_last_qubits, if_pos rfl, init_snoc_qubits]
        simp_rw [snoc_castSucc_qubits]
        exact qftQubits_step n j k
      · intro z hz
        rw [embedOp_hadApp_last, diagonal_mul_apply, liftInit_apply]
        by_cases hinit : Fin.init y0 = Fin.init z
        · by_cases hlast : z (Fin.last n) = k (Fin.last n)
          · exfalso
            apply hz
            apply (eq_iff_init_eq_and_last_eq z z0).2
            refine ⟨?_, ?_⟩
            · dsimp only [y0, z0] at hinit ⊢
              rw [← hinit, init_snoc_qubits, init_snoc_qubits]
            · dsimp only [z0]
              rw [hlast, snoc_last_qubits]
          · rw [if_neg hlast, mul_zero, mul_zero]
        · rw [if_neg hinit, zero_mul]

end SolQFTCircuitExact

theorem section5_qft_circuit_proved (n : ℕ) :
    ∃ c : Circuit qftGateSet n, c.unitary = qftQubits n ∧ c.size ≤ n ^ 2 :=
  ⟨SolQFTCircuitExact.qftCircuit n,
    SolQFTCircuitExact.qftCircuit_unitary n,
    SolQFTCircuitExact.qftCircuit_size n⟩


end
set_option autoImplicit false
open QAlgorithms QuantumLTF.Membership Thm49Primitives
theorem solution (q : ℕ) :
    ∃ c : Circuit gates12 q, c.size ≤ q^2 ∧ c.unitary=qftQubits q := by
  obtain ⟨c,hu,hs⟩ := section5_qft_circuit_proved q
  exact ⟨section5_change_gate_set section5_qft_gates_elementary c,
    (section5_change_gate_set_size _ _).le.trans hs,
    (section5_change_gate_set_unitary _ _).trans hu⟩
