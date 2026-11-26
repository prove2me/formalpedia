-- Prove2me | solution 1 for section5_embed_classical_gate_action
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T19:50:07.375563+00:00
-- url     : https://prove2.me/submissions/7a43df76-f619-4b6e-805b-9d47fe89ca44

import Definitions.Def_QAlgorithms_Defs_Classical
import Definitions.Def_QuantumLTF_Membership_gatesRev
import Definitions.Def_Section5Verified_Section5ReversibleBooleanCompiler
import Mathlib
set_option autoImplicit false
open QAlgorithms QuantumLTF.Membership
theorem solution {k m : ℕ} (e : Fin k ↪ Fin m)
    (M : Matrix (Qubits k) (Qubits k) ℂ) (f : Qubits k → Qubits k)
    (hM : ∀ y z, M y z=if y=f z then 1 else 0) (x : Qubits m) :
    act (embedOp M e) (ket x)=ket (section5_replace_wires e x (f (x ∘ e))) := by
  classical
  ext y
  change Matrix.mulVec (embedOp M e) (Pi.single x (1:ℂ)) y =
    (Pi.single (section5_replace_wires e x (f (x ∘ e))) (1:ℂ) : Qubits m → ℂ) y
  rw [Matrix.mulVec_single]
  simp only [MulOpposite.op_one,one_smul]
  have hcond : ((∀ i : Fin m, i ∉ Set.range e → y i=x i) ∧ y ∘ e=f (x ∘ e)) ↔
      y=section5_replace_wires e x (f (x ∘ e)) := by
    constructor
    · rintro ⟨hoff,hon⟩
      funext i
      by_cases hi : i ∈ Set.range e
      · obtain ⟨j,rfl⟩ := hi
        rw [section5_replace_wires_on]
        exact congrFun hon j
      · rw [section5_replace_wires_off e x _ i hi]
        exact hoff i hi
    · intro hy
      subst y
      constructor
      · intro i hi
        exact section5_replace_wires_off e x _ i hi
      · funext j
        exact section5_replace_wires_on e x _ j
  change (if ∀ i : Fin m, i ∉ Set.range e → y i=x i then M (y ∘ e) (x ∘ e) else 0) = _
  rw [hM]
  simp only [ite_and,← hcond,Pi.single_apply,eq_comm]
