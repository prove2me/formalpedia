-- Prove2me | solution 1 for witt_ring_structure
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:12:52.06532+00:00
-- url     : https://prove2.me/submissions/637c450a-d77e-4ab6-9421-6e0d5e6cfbf6

import Definitions.Def_Formalism_PeriodIntegrals_WfRing
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExponentialIntegrality_InvNatMemWf
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_WfRing
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
private theorem exists_pow_mul_add_mem_subring {R : Type*} [CommRing R] (S : Subring R) (q : R) (hq : q ∈ S) {a b : R}
    (ha : ∃ k : ℕ, q ^ k * a ∈ S) (hb : ∃ k : ℕ, q ^ k * b ∈ S) : ∃ k : ℕ, q ^ k * (a + b) ∈ S := by
  obtain ⟨i, hi⟩ := ha
  obtain ⟨j, hj⟩ := hb
  refine ⟨i + j, ?_⟩
  have e : q ^ (i + j) * (a + b) = q ^ j * (q ^ i * a) + q ^ i * (q ^ j * b) := by ring
  rw [e]
  exact S.add_mem (S.mul_mem (S.pow_mem hq _) hi) (S.mul_mem (S.pow_mem hq _) hj)
private theorem exists_pow_mul_sub_mem_subring {R : Type*} [CommRing R] (S : Subring R) (q : R) (hq : q ∈ S) {a b : R}
    (ha : ∃ k : ℕ, q ^ k * a ∈ S) (hb : ∃ k : ℕ, q ^ k * b ∈ S) : ∃ k : ℕ, q ^ k * (a - b) ∈ S := by
  obtain ⟨i, hi⟩ := ha
  obtain ⟨j, hj⟩ := hb
  refine ⟨i + j, ?_⟩
  have e : q ^ (i + j) * (a - b) = q ^ j * (q ^ i * a) - q ^ i * (q ^ j * b) := by ring
  rw [e]
  exact S.sub_mem (S.mul_mem (S.pow_mem hq _) hi) (S.mul_mem (S.pow_mem hq _) hj)
private theorem exists_pow_mul_mul_mem_subring {R : Type*} [CommRing R] (S : Subring R) {q a b : R}
    (ha : ∃ k : ℕ, q ^ k * a ∈ S) (hb : ∃ k : ℕ, q ^ k * b ∈ S) : ∃ k : ℕ, q ^ k * (a * b) ∈ S := by
  obtain ⟨i, hi⟩ := ha
  obtain ⟨j, hj⟩ := hb
  refine ⟨i + j, ?_⟩
  have e : q ^ (i + j) * (a * b) = (q ^ i * a) * (q ^ j * b) := by ring
  rw [e]
  exact S.mul_mem hi hj
private theorem exists_pow_mul_finset_sum_mem_subring {R : Type*} [CommRing R] (S : Subring R) (q : R) (hq : q ∈ S) {ι : Type*}
    (s : Finset ι) (f : ι → R) (h : ∀ i ∈ s, ∃ k : ℕ, q ^ k * f i ∈ S) :
    ∃ k : ℕ, q ^ k * ∑ i ∈ s, f i ∈ S := by
  classical
  revert h
  refine Finset.induction_on s (fun _ => ⟨0, by simp⟩) ?_
  intro a s ha ih h
  rw [Finset.sum_insert ha]
  exact exists_pow_mul_add_mem_subring S q hq (h a (Finset.mem_insert_self a s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))
end

set_option autoImplicit false

theorem _root_.solution : PI.WfRing := by
  classical
  intro p _ σ f g hf hg
  delta PI.CoefWf PI.InWf at hf hg ⊢
  have hq : (p : ℂ_[p]) ∈ PI.Wp p := natCast_mem (PI.Wp p) p
  refine ⟨fun n => ?_, fun n => ?_, fun n => ?_, fun c hc n => ?_⟩
  · rw [map_add]
    exact exists_pow_mul_add_mem_subring _ _ hq (hf n) (hg n)
  · rw [map_sub]
    exact exists_pow_mul_sub_mem_subring _ _ hq (hf n) (hg n)
  · rw [MvPowerSeries.coeff_mul]
    exact exists_pow_mul_finset_sum_mem_subring _ _ hq _ _ fun x _ => exists_pow_mul_mul_mem_subring _ (hf x.1) (hg x.2)
  · rw [MvPowerSeries.coeff_C_mul]
    exact exists_pow_mul_mul_mem_subring _ hc (hf n)
