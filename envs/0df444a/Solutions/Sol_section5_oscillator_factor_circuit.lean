-- Prove2me | solution 1 for section5_oscillator_factor_circuit
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T20:09:53.529781+00:00
-- url     : https://prove2.me/submissions/16036930-079d-4d98-86fa-883dfd8fb2f6

import Definitions.Def_QAlgorithms_Defs_Fourier
import Definitions.Def_QuantumLTF_Example_HermiteModel
import Definitions.Def_QuantumLTF_Membership_Supplement_thm49_primitives
import Definitions.Def_QuantumLTF_Membership_gates12
import Definitions.Def_Section5Verified_Section5OscillatorFactors
import Definitions.Def_Section5Verified_Section5QuadraticPhase
import Mathlib
import Theorems.Thm_section5_discrete_momentum_evolution
import Theorems.Thm_section5_discrete_position_evolution
set_option autoImplicit false
open QAlgorithms QuantumLTF.Membership Thm49Primitives
theorem solution (q : ℕ) (hq : 0 < q) (a b : ℝ) :
    ∃ c : Circuit gates12 q, c.size ≤ 7*q^2+11*q+7 ∧
      c.unitary=section5_oscillator_chirps q a b := by
  obtain ⟨p,hp,hpu⟩ := section5_discrete_momentum_evolution q hq a
  obtain ⟨x,hx,hxu⟩ := section5_discrete_position_evolution q hq b
  refine ⟨p++x++p,?_,?_⟩
  · simp only [Circuit.size,List.length_append]
    change p.length ≤ _ at hp
    change x.length=_ at hx
    omega
  · rw [circuit_unitary_append,circuit_unitary_append,hpu,hxu]
    simp only [section5_oscillator_chirps,section5_position_chirp,mul_assoc]
