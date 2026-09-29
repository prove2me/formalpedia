-- Prove2me | solution 1 for mme_type2_threeAP_hash_retains_ambient_completion
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-02T22:06:19.59305+00:00
-- url     : https://prove2.me/submissions/b0c9a66f-483d-4c40-9ccb-a91cba502a00

import Mathlib
import Theorems.Thm_mme_threeAP_free_half_modulus_no_collision

set_option autoImplicit false
set_option warningAsError true

theorem solution
    {Edge : Type*} {Vertex : Fin 3 → Type*}
    (M : ℕ) (S : Finset ℕ)
    (hSrange : S ⊆ Finset.range (M / 2))
    (hSfree : ThreeAPFree (S : Set ℕ))
    (vertex : ∀ i, Edge → Vertex i)
    (supportedMix : Edge → Edge → Edge → Prop)
    (hash : ∀ i, Vertex i → ZMod M)
    (retained : Edge → Prop)
    (hretained : ∀ e, retained e ↔
      ∃ s ∈ S, ∀ i : Fin 3,
        hash i (vertex i e) = (s : ZMod M))
    (hAP : ∀ x y z, supportedMix x y z →
      hash 0 (vertex 0 x) + hash 1 (vertex 1 y) =
        2 * hash 2 (vertex 2 z))
    (ambient : Finset Edge)
    (x y z : Edge) (hx : retained x) (hy : retained y)
    (hz : retained z) (hsupp : supportedMix x y z)
    (hcomplete : ∃ e ∈ ambient,
      vertex 0 e = vertex 0 x ∧
      vertex 1 e = vertex 1 y ∧
      vertex 2 e = vertex 2 z) :
    ∃ e ∈ ambient, retained e ∧
      vertex 0 e = vertex 0 x ∧
      vertex 1 e = vertex 1 y ∧
      vertex 2 e = vertex 2 z := by
  obtain ⟨sx, hsx, hxs⟩ := (hretained x).mp hx
  obtain ⟨sy, hsy, hys⟩ := (hretained y).mp hy
  obtain ⟨sz, hsz, hzs⟩ := (hretained z).mp hz
  have hprog := hAP x y z hsupp
  rw [hxs 0, hys 1, hzs 2] at hprog
  obtain ⟨hxz, hzy⟩ :=
    mme_threeAP_free_half_modulus_no_collision
      M S hSrange hSfree sx sz sy hsx hsz hsy hprog
  obtain ⟨e, heAmbient, he0, he1, he2⟩ := hcomplete
  refine ⟨e, heAmbient, (hretained e).mpr ⟨sx, hsx, ?_⟩,
    he0, he1, he2⟩
  intro i
  fin_cases i
  · change hash 0 (vertex 0 e) = (sx : ZMod M)
    rw [he0, hxs 0]
  · change hash 1 (vertex 1 e) = (sx : ZMod M)
    rw [he1, hys 1, ← hzy, ← hxz]
  · change hash 2 (vertex 2 e) = (sx : ZMod M)
    rw [he2, hzs 2, ← hxz]
