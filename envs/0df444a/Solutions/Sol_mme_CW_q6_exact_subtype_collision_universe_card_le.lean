-- Prove2me | solution 1 for mme_CW_q6_exact_subtype_collision_universe_card_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-25T00:27:36.412053+00:00
-- url     : https://prove2.me/submissions/5fca493e-427f-4e48-aa1a-12db783cd47a

import Mathlib
import Theorems.Thm_mme_finset_two_mode_collision_pairs_card_le_of_fiber_degree
import Definitions.Def_mme_CW_q6_exact_address_incidence

open MME

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable local instance q6CollisionUniverseSolutionExactAddressDecidableEq
    (N L G : ℕ) : DecidableEq (CWQ6ExactCoupledAddress N L G) :=
  Classical.decEq _

noncomputable local instance q6CollisionUniverseSolutionCoupledAddressFintype
    (N : ℕ) : Fintype (CWQ6CoupledAddress N) :=
  inferInstanceAs (Fintype (Fin 3 → Fin (2 * N) → Fin 3))

noncomputable local instance q6CollisionUniverseSolutionExactAddressFintype
    (N L G : ℕ) : Fintype (CWQ6ExactCoupledAddress N L G) :=
  Fintype.ofInjective (fun e => e.1) Subtype.val_injective

/-- Exact q=6 regularity bounds the complete ordered X/Y collision universe
by twice the exact edge count times the common X/Y degree. -/
theorem solution
    (N L G : ℕ)
    (hregular : CWQ6ExactAddressRegularity N L G) :
    let E : Finset (CWQ6ExactCoupledAddress N L G) := Finset.univ
    ((E.product E).filter (fun p =>
      p.1 ≠ p.2 ∧
        (p.1.1 0 = p.2.1 0 ∨ p.1.1 1 = p.2.1 1))).card ≤
      2 *
        ((Nat.choose (2 * N) L * Nat.choose (2 * N - L) L) *
          Nat.choose (2 * G) G) *
        (Nat.choose N G) ^ 2 := by
  classical
  let E : Finset (CWQ6ExactCoupledAddress N L G) := Finset.univ
  have hExact (e : CWQ6ExactCoupledAddress N L G) :
      e.1 ∈ cwQ6ExactAddresses N L G := by
    simp only [cwQ6ExactAddresses, Finset.mem_filter, Finset.mem_univ,
      true_and]
    exact e.2
  have hEimage : E.image (fun e => e.1) = cwQ6ExactAddresses N L G := by
    ext a
    constructor
    · intro ha
      obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp ha
      exact hExact e
    · intro ha
      have hprops :
          CWQ6CoupledCoordinatewiseSupported a ∧
            ∀ i r : Fin 3,
              (Finset.univ.filter (fun j : Fin (2 * N) => a i j = r)).card =
                cwQ6CoupledMarginalMultiplicity N L G i r := by
        simpa only [cwQ6ExactAddresses, Finset.mem_filter,
          Finset.mem_univ, true_and] using ha
      let e : CWQ6ExactCoupledAddress N L G := ⟨a, hprops⟩
      exact Finset.mem_image.mpr ⟨e, (by simp [E]), rfl⟩
  have hEcard : E.card =
      (Nat.choose (2 * N) L * Nat.choose (2 * N - L) L) *
        Nat.choose (2 * G) G := by
    calc
      E.card = (E.image (fun e => e.1)).card :=
        (Finset.card_image_of_injective _ Subtype.val_injective).symm
      _ = (cwQ6ExactAddresses N L G).card := congrArg Finset.card hEimage
      _ = _ := hregular.total_card
  have hxdeg : ∀ e ∈ E,
      (E.filter (fun f => f.1 0 = e.1 0)).card ≤ (Nat.choose N G) ^ 2 := by
    intro e he
    let F := E.filter (fun f => f.1 0 = e.1 0)
    let Fraw := (cwQ6ExactAddresses N L G).filter (fun a => a 0 = e.1 0)
    have himage : F.image (fun f => f.1) = Fraw := by
      ext a
      constructor
      · intro ha
        obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp ha
        have hf' := Finset.mem_filter.mp hf
        exact Finset.mem_filter.mpr ⟨hExact f, hf'.2⟩
      · intro ha
        have ha' := Finset.mem_filter.mp ha
        have hprops :
            CWQ6CoupledCoordinatewiseSupported a ∧
              ∀ i r : Fin 3,
                (Finset.univ.filter (fun j : Fin (2 * N) => a i j = r)).card =
                  cwQ6CoupledMarginalMultiplicity N L G i r := by
          simpa only [cwQ6ExactAddresses, Finset.mem_filter,
            Finset.mem_univ, true_and] using ha'.1
        let f : CWQ6ExactCoupledAddress N L G := ⟨a, hprops⟩
        exact Finset.mem_image.mpr ⟨f,
          Finset.mem_filter.mpr ⟨(by simp [E]), ha'.2⟩, rfl⟩
    have hxmem : e.1 0 ∈ cwQ6ExactXWords N L G := by
      exact Finset.mem_image.mpr ⟨e.1, hExact e, rfl⟩
    have hcardF : F.card = Fraw.card := by
      calc
        F.card = (F.image (fun f => f.1)).card :=
          (Finset.card_image_of_injective _ Subtype.val_injective).symm
        _ = Fraw.card := congrArg Finset.card himage
    change F.card ≤ _
    rw [hcardF, hregular.x_degree (e.1 0) hxmem]
  have hydeg : ∀ e ∈ E,
      (E.filter (fun f => f.1 1 = e.1 1)).card ≤ (Nat.choose N G) ^ 2 := by
    intro e he
    let F := E.filter (fun f => f.1 1 = e.1 1)
    let Fraw := (cwQ6ExactAddresses N L G).filter (fun a => a 1 = e.1 1)
    have himage : F.image (fun f => f.1) = Fraw := by
      ext a
      constructor
      · intro ha
        obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp ha
        have hf' := Finset.mem_filter.mp hf
        exact Finset.mem_filter.mpr ⟨hExact f, hf'.2⟩
      · intro ha
        have ha' := Finset.mem_filter.mp ha
        have hprops :
            CWQ6CoupledCoordinatewiseSupported a ∧
              ∀ i r : Fin 3,
                (Finset.univ.filter (fun j : Fin (2 * N) => a i j = r)).card =
                  cwQ6CoupledMarginalMultiplicity N L G i r := by
          simpa only [cwQ6ExactAddresses, Finset.mem_filter,
            Finset.mem_univ, true_and] using ha'.1
        let f : CWQ6ExactCoupledAddress N L G := ⟨a, hprops⟩
        exact Finset.mem_image.mpr ⟨f,
          Finset.mem_filter.mpr ⟨(by simp [E]), ha'.2⟩, rfl⟩
    have hymem : e.1 1 ∈ cwQ6ExactYWords N L G := by
      exact Finset.mem_image.mpr ⟨e.1, hExact e, rfl⟩
    have hcardF : F.card = Fraw.card := by
      calc
        F.card = (F.image (fun f => f.1)).card :=
          (Finset.card_image_of_injective _ Subtype.val_injective).symm
        _ = Fraw.card := congrArg Finset.card himage
    change F.card ≤ _
    rw [hcardF, hregular.y_degree (e.1 1) hymem]
  have hbound := mme_finset_two_mode_collision_pairs_card_le_of_fiber_degree
    E (fun e => e.1 0) (fun e => e.1 1)
      ((Nat.choose N G) ^ 2) hxdeg hydeg
  simpa only [hEcard] using hbound
