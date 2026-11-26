-- Prove2me | solution 1 for section5_discrete_momentum_evolution
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T20:07:23.127802+00:00
-- url     : https://prove2.me/submissions/3b0c04e3-a621-47c3-8534-d4cb4dd00c7a

import Definitions.Def_QAlgorithms_Defs_Fourier
import Definitions.Def_QuantumLTF_Example_HermiteModel
import Definitions.Def_QuantumLTF_Membership_Supplement_thm49_primitives
import Definitions.Def_QuantumLTF_Membership_gates12
import Definitions.Def_Section5Verified_Section5FourierCircuit
import Definitions.Def_Section5Verified_Section5OscillatorFactors
import Definitions.Def_Section5Verified_Section5QuadraticPhase
import Mathlib
import Theorems.Thm_section5_discrete_position_evolution
import Theorems.Thm_section5_elementary_centered_qft
section
set_option autoImplicit false

open QAlgorithms QuantumLTF.Membership Thm49Primitives

/-! Exact circuits for the position and momentum chirps in the discrete oscillator
factorization. Their approximation to oscillator evolution is a separate analytic
claim and is not asserted by these circuit identities. -/



theorem section5_elementary_adjoint_size {n : ℕ} (c : Circuit gates12 n) :
    (section5_elementary_adjoint c).size=c.size := by
  simp [section5_elementary_adjoint,Circuit.size]

theorem section5_elementary_adjoint_unitary {n : ℕ} (c : Circuit gates12 n) :
    (section5_elementary_adjoint c).unitary=star c.unitary := by
  induction c with
  | nil => simp [section5_elementary_adjoint,Circuit.unitary]
  | cons g c ih =>
    simp only [section5_elementary_adjoint,List.map_cons,List.reverse_cons] at ih ⊢
    rw [circuit_unitary_append,circuit_unitary_cons,circuit_unitary_nil,one_mul,
      circuit_unitary_cons,star_mul,ih]
    simp only [Thm49Primitives.GateApp.adj,embedOp_star]

















end
set_option autoImplicit false
open QAlgorithms QuantumLTF.Membership Thm49Primitives
theorem solution (q : ℕ) (hq : 0 < q) (t : ℝ) :
    ∃ c : Circuit gates12 q, c.size ≤ 3*q^2+5*q+3 ∧
      c.unitary=section5_momentum_chirp q t := by
  obtain ⟨f,hf,hfu⟩ := section5_elementary_centered_qft q hq
  obtain ⟨d,hd,hdu⟩ := section5_discrete_position_evolution q hq t
  refine ⟨f++d++section5_elementary_adjoint f,?_,?_⟩
  · simp only [Circuit.size,List.length_append]
    have ha := section5_elementary_adjoint_size f
    change (section5_elementary_adjoint f).length=f.length at ha
    change f.length ≤ _ at hf
    change d.length=_ at hd
    omega
  · rw [circuit_unitary_append,circuit_unitary_append,section5_elementary_adjoint_unitary,hfu,hdu]
    simp only [section5_momentum_chirp,section5_position_chirp,mul_assoc]
