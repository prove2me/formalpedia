-- Prove2me | solution 1 for mme_stothers_phi233_retained_target_ambient_closure
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-03T00:15:50.087196+00:00
-- url     : https://prove2.me/submissions/2c12f8c3-7d60-4165-987e-ad113e5f71b1

import Mathlib.Tactic
import Definitions.Def_mme_stothers_phi233_hash_retention_data
import Theorems.Thm_mme_stothers_phi233_cyclic_affine_hash_AP
import Theorems.Thm_mme_stothers_phi233_cyclic_affine_hash_normal_form
import Theorems.Thm_mme_stothers_phi233_cyclic_target_ambient_closure

open MME.StothersFourth.Phi233

set_option autoImplicit false
set_option warningAsError true

theorem solution
    {p N alpha beta gamma delta : ℕ}
    (S : Finset (ZMod p))
    (hSfree : ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S,
      a + b = 2 * c → a = c ∧ c = b)
    (q : HashState p N) :
    ∀ x ∈ retainedTarget p N alpha beta gamma delta S q,
      ∀ y ∈ retainedTarget p N alpha beta gamma delta S q,
        ∀ z ∈ retainedTarget p N alpha beta gamma delta S q,
          CyclicCoordinatewiseSupported x y z →
            ∃ e ∈ retainedAmbient p N alpha beta gamma delta S q,
              cyclicModeWord e 0 = cyclicModeWord x 0 ∧
              cyclicModeWord e 1 = cyclicModeWord y 1 ∧
              cyclicModeWord e 2 = cyclicModeWord z 2 := by
  classical
  intro x hx y hy z hz hsupp
  have hx' : x ∈ targetFinset N alpha beta gamma delta ∧
      Retained p N alpha beta gamma delta S q x := by
    simpa only [retainedTarget, Finset.mem_filter] using hx
  have hy' : y ∈ targetFinset N alpha beta gamma delta ∧
      Retained p N alpha beta gamma delta S q y := by
    simpa only [retainedTarget, Finset.mem_filter] using hy
  have hz' : z ∈ targetFinset N alpha beta gamma delta ∧
      Retained p N alpha beta gamma delta S q z := by
    simpa only [retainedTarget, Finset.mem_filter] using hz
  obtain ⟨sx, hsx, hxs⟩ := hx'.2
  obtain ⟨sy, hsy, hys⟩ := hy'.2
  obtain ⟨sz, hsz, hzs⟩ := hz'.2
  have hap :
      stateHash p N alpha beta gamma delta q 0 x +
          stateHash p N alpha beta gamma delta q 1 y =
        2 * stateHash p N alpha beta gamma delta q 2 z := by
    simpa only [stateHash] using
      (mme_stothers_phi233_cyclic_affine_hash_AP
        (stateWeights q) (stateShift q) ((6 : ZMod p)⁻¹ * q.2)
        x y z hsupp)
  have hlabels : sx = sz ∧ sz = sy := by
    apply hSfree sx hsx sy hsy sz hsz
    simpa only [hxs 0, hys 1, hzs 2] using hap
  obtain ⟨e, heAmbient, he0, he1, he2⟩ :=
    (mme_stothers_phi233_cyclic_target_ambient_closure
      N alpha beta gamma delta).2
      x hx'.1 y hy'.1 z hz'.1 hsupp
  have hvertex (i : Fin 3)
      (a b : CyclicAmbientEdge N alpha beta gamma delta)
      (hab : cyclicModeWord a i = cyclicModeWord b i) :
      stateHash p N alpha beta gamma delta q i a =
        stateHash p N alpha beta gamma delta q i b := by
    unfold stateHash
    rw [mme_stothers_phi233_cyclic_affine_hash_normal_form
      (stateWeights q) (stateShift q) ((6 : ZMod p)⁻¹ * q.2) i a]
    rw [mme_stothers_phi233_cyclic_affine_hash_normal_form
      (stateWeights q) (stateShift q) ((6 : ZMod p)⁻¹ * q.2) i b]
    rw [hab]
  refine ⟨e, ?_, he0, he1, he2⟩
  simp only [retainedAmbient, Finset.mem_filter]
  refine ⟨heAmbient, ⟨sx, hsx, ?_⟩⟩
  intro i
  fin_cases i
  · exact (hvertex 0 e x he0).trans (hxs 0)
  · exact (hvertex 1 e y he1).trans
      ((hys 1).trans (hlabels.2.symm.trans hlabels.1.symm))
  · exact (hvertex 2 e z he2).trans
      ((hzs 2).trans hlabels.1.symm)
