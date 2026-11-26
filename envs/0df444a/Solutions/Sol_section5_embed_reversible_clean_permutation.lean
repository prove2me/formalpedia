-- Prove2me | solution 1 for section5_embed_reversible_clean_permutation
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T19:38:45.858101+00:00
-- url     : https://prove2.me/submissions/0e007c7e-89a1-4598-a9df-a43bea2a8323

import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QAlgorithms_Defs_Circuit
import Definitions.Def_QAlgorithms_Defs_Classical
import Definitions.Def_QuantumLTF_Membership_Supplement_bitonicTrace54
import Definitions.Def_QuantumLTF_Membership_Supplement_lcgSym54ArithV2
import Definitions.Def_QuantumLTF_Membership_Supplement_symBand54
import Definitions.Def_QuantumLTF_Membership_Supplement_thm410_router_blocks
import Definitions.Def_QuantumLTF_Membership_Supplement_thm49_primitives
import Definitions.Def_QuantumLTF_Membership_flatReg
import Definitions.Def_QuantumLTF_Membership_gates12
import Definitions.Def_QuantumLTF_Membership_gatesRev
import Definitions.Def_QuantumLTF_Membership_splitReg
import Definitions.Def_Section5Verified_Section5ClassicalArithmeticRealization
import Mathlib
section
set_option autoImplicit false

open QAlgorithms QuantumLTF.Membership Thm49Primitives

/-! Reusing the accepted arithmetic circuits in the actual classical postprocessing gate set. -/





theorem section5_rev_map_wires_size {m n : ℕ} (e : Fin m ↪ Fin n) (c : Circuit gatesRev m) :
    (section5_rev_map_wires e c).size=c.size := by simp [section5_rev_map_wires,Circuit.size]

theorem section5_rev_map_wires_unitary {m n : ℕ} (e : Fin m ↪ Fin n) (c : Circuit gatesRev m) :
    (section5_rev_map_wires e c).unitary=embedOp c.unitary e := by
  induction c with
  | nil => simp [section5_rev_map_wires,Circuit.unitary,embedOp_one]
  | cons g c ih =>
    simp only [section5_rev_map_wires,List.map_cons,circuit_unitary_cons] at ih ⊢
    rw [ih,embedOp_mul,embedOp_embedOp]























end
section
set_option autoImplicit false

/-! Reused accepted arithmetic proof by Robin Kothari, submission 0ac99132-8635-4775-91de-dd0ad0e55353.
Apache-2.0. This local dependency is not a new contribution.
Helper definitions are exposed to verify their realization over gatesRev. -/

namespace Aux_w54_arith

open QAlgorithms QuantumLTF.Membership QuantumLTF.Membership.Supplement
open QuantumLTF.Membership.Supplement.LcgSym54 Thm49Primitives Thm410Router

lemma act_subReg_perm {main anc m : ℕ} (lc : LayeredCircuit (main + anc))
    (f : Qubits main → Qubits main) (hlc : lc.ImplementsOnClean (permMat f))
    (embMain : Fin main ↪ Fin m) (embAnc : Fin anc ↪ Fin m)
    (hdisj : ∀ i j, embMain i ≠ embAnc j) (z : Qubits m)
    (hclean : ∀ j : Fin anc, z (embAnc j) = false) :
    act (lc.mapWires (combineEmb embMain embAnc hdisj)).unitary (ket z) =
      ket (updateOn embMain z (f (z ∘ embMain))) := by
  have hact := act_mapWires_implementsOnClean lc (permMat f) hlc
    (combineEmb embMain embAnc hdisj) z (fun j => by simpa using hclean j)
  dsimp only at hact
  rw [hact, Finset.sum_eq_single (f (z ∘ ((Fin.castAddEmb anc).trans (combineEmb embMain embAnc hdisj))))]
  · simp [permMat, castAddEmb_trans_combineEmb]
  · intro y _ hy; simp [permMat, hy]
  · intro hm; exact absurd (Finset.mem_univ _) hm


























/-! ### Part 2: Zero-Ancilla Register Primitives -/












































































/-! ### Part 3: Equality, Constant Comparison & Particle Encoding -/
































/-! ### Part 4: Recursive Cuccaro In-Place Adder & Unsigned Comparator -/

















































































/-! ### Part 5: Sub-register Combinators, Controlled Arithmetic & Bit-Reversal -/



















































































/-! ### MSB-First Circuit Wrappers via Zero-Gate `Fin.revPerm` Conjugation -/













-- 1. setConstMSBCircuit






-- 2. ctrlConstXorMSBCircuit






-- 3. eqConstMSBCircuit






-- 4. ltConstMSBCircuit






-- 5. ltRegMSBCircuit






-- 6 & 7. addInPlaceMSBCircuit & subInPlaceMSBCircuit
















-- 8 & 9. ctrlAddInPlaceMSBCircuit & ctrlSubInPlaceMSBCircuit
















-- 10 & 11. ctrlAddConstInPlaceMSBCircuit & ctrlSubConstInPlaceMSBCircuit












end Aux_w54_arith

open QAlgorithms QuantumLTF.Membership QuantumLTF.Membership.Supplement
open QuantumLTF.Membership.Supplement.LcgSym54 Aux_w54_arith




end
set_option autoImplicit false
open QAlgorithms QuantumLTF.Membership Thm49Primitives Thm410Router
open QuantumLTF.Membership.Supplement.LcgSym54
theorem solution {main anc m : ℕ}
    (lc : LayeredCircuit (main+anc)) (f : Qubits main → Qubits main)
    (hrev : section5_RevRealizable lc) (hlc : lc.ImplementsOnClean (permMat f))
    (eMain : Fin main ↪ Fin m) (eAnc : Fin anc ↪ Fin m)
    (hdisj : ∀ i j, eMain i ≠ eAnc j) :
    ∃ c : Circuit gatesRev m, c.size ≤ lc.size ∧
      ∀ z : Qubits m, (∀ j, z (eAnc j)=false) →
        act c.unitary (ket z)=ket (updateOn eMain z (f (z ∘ eMain))) := by
  obtain ⟨c,hc,hcu⟩ := hrev
  let e := combineEmb eMain eAnc hdisj
  refine ⟨section5_rev_map_wires e c,?_,?_⟩
  · simpa only [section5_rev_map_wires_size] using hc
  · intro z hz
    rw [section5_rev_map_wires_unitary,hcu,← LayeredCircuit.mapWires_unitary]
    exact Aux_w54_arith.act_subReg_perm lc f hlc eMain eAnc hdisj z hz
