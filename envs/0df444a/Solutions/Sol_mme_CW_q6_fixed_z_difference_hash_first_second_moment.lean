-- Prove2me | solution 1 for mme_CW_q6_fixed_z_difference_hash_first_second_moment
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-24T22:38:33.826853+00:00
-- url     : https://prove2.me/submissions/4ec78ca8-ac2c-4b03-aab9-c3376f5053c1

import Theorems.Thm_mme_finite_injective_linear_code_first_second_moment
import Theorems.Thm_mme_CW_q6_difference_code_has_unit_coefficient
import Theorems.Thm_mme_CW_q6_fixed_z_difference_code_injective
import Theorems.Thm_mme_CW_q6_fixed_z_nondependent_pair_unit_minor

open BigOperators MME

set_option autoImplicit false

/-- Exact first moment and a source-scale second-moment upper bound for the
q=6 X-minus-Z hash equations in one fixed Z-fiber. -/
theorem solution
    {M n L G : ℕ} [NeZero M]
    (hM : 2 < M) (h2 : IsUnit (2 : ZMod M)) (hG : 0 < G)
    (A : Finset (CWQ6ExactCoupledAddress (n + 1) L G))
    (z : Fin (2 * (n + 1)) → Fin 3)
    (hz : ∀ e ∈ A, e.1 2 = z) :
    let c : {e // e ∈ A} → Fin (2 * n + 2) → ZMod M := fun e j =>
      (2 * ((e.1.1 0 j).val : ZMod M)) -
        (cwQ6CoupledZHashCode (e.1.1 2 j) : ZMod M)
    (∑ w : Fin (2 * n + 2) → ZMod M,
        (A.attach.filter (fun e => ∑ i, c e i * w i = 0)).card) =
          A.card * M ^ (2 * n + 1) ∧
    (∑ w : Fin (2 * n + 2) → ZMod M,
        (A.attach.filter (fun e => ∑ i, c e i * w i = 0)).card ^ 2) ≤
          2 * A.card * M ^ (2 * n + 1) + A.card ^ 2 * M ^ (2 * n) := by
  classical
  let c : {e // e ∈ A} → Fin (2 * n + 2) → ZMod M := fun e j =>
    (2 * ((e.1.1 0 j).val : ZMod M)) -
      (cwQ6CoupledZHashCode (e.1.1 2 j) : ZMod M)
  have hunit : ∀ e ∈ A.attach, ∃ j, IsUnit (c e j) := by
    intro e he
    exact mme_CW_q6_difference_code_has_unit_coefficient (M := M) e.1 hG
  have hinj : Function.Injective c := by
    intro e f hef
    apply Subtype.ext
    apply mme_CW_q6_fixed_z_difference_code_injective hM h2 e.1 f.1
    · exact (hz e.1 e.2).trans (hz f.1 f.2).symm
    · exact hef
  have hminor : ∀ e ∈ A.attach, ∀ f ∈ A.attach,
      c e ≠ c f → c e ≠ (fun i => -c f i) →
      ∃ j k, IsUnit (c e j * c f k - c e k * c f j) := by
    intro e he f hf hne hnneg
    have hne' :
        (fun j =>
          (2 * ((e.1.1 0 j).val : ZMod M)) -
            (cwQ6CoupledZHashCode (e.1.1 2 j) : ZMod M)) ≠
        (fun j =>
          (2 * ((f.1.1 0 j).val : ZMod M)) -
            (cwQ6CoupledZHashCode (f.1.1 2 j) : ZMod M)) := by
      exact hne
    have hnneg' :
        (fun j =>
          (2 * ((e.1.1 0 j).val : ZMod M)) -
            (cwQ6CoupledZHashCode (e.1.1 2 j) : ZMod M)) ≠
        (fun j => -(
          (2 * ((f.1.1 0 j).val : ZMod M)) -
            (cwQ6CoupledZHashCode (f.1.1 2 j) : ZMod M))) := by
      exact hnneg
    exact mme_CW_q6_fixed_z_nondependent_pair_unit_minor e.1 f.1
        ((hz e.1 e.2).trans (hz f.1 f.2).symm) hne' hnneg' h2
  simpa only [c, Finset.card_attach] using
    mme_finite_injective_linear_code_first_second_moment
      (M := M) (n := 2 * n) A.attach c hunit hinj hminor
