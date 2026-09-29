-- Prove2me | solution 1 for mme_CW_q6_z_hash_offset_label_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-24T23:02:15.799158+00:00
-- url     : https://prove2.me/submissions/b6a28f97-2c7c-4299-9be2-98a454e3e560

import Mathlib
import Definitions.Def_mme_CW_q6_doubled_hash_arithmetic

open BigOperators MME

set_option autoImplicit false

/-- For fixed weights and one Z-word, exactly one offset per retained label
makes the doubled Z-hash land on that label. -/
theorem solution
    {M N : ℕ} [NeZero M]
    (h2 : IsUnit (2 : ZMod M))
    (S : Finset ℕ) (hSrange : S ⊆ Finset.range M)
    (w : Fin (2 * N) → ZMod M)
    (z : Fin (2 * N) → Fin 3) :
    ((Finset.univ : Finset (ZMod M)).filter (fun b0 =>
      ∃ s ∈ S,
        cwQ6DoubledZHash b0 w z = 2 * (s : ZMod M))).card = S.card := by
  classical
  let T : Finset (ZMod M) :=
    S.image (fun (s : ℕ) => 2 * (s : ZMod M))
  have hTcard : T.card = S.card := by
    change (S.image (fun (s : ℕ) => 2 * (s : ZMod M))).card = S.card
    apply Finset.card_image_iff.mpr
    intro a ha b hb hab
    have hab' : (a : ZMod M) = (b : ZMod M) := h2.mul_left_cancel hab
    exact (ZMod.natCast_eq_natCast_iff a b M).mp hab'
      |>.eq_of_lt_of_lt (Finset.mem_range.mp (hSrange ha))
        (Finset.mem_range.mp (hSrange hb))
  let t : ZMod M :=
    ∑ j, (cwQ6CoupledZHashCode (z j) : ZMod M) * w j
  let e : ZMod M ≃ ZMod M :=
    (Units.mulLeft h2.unit).trans (Equiv.addRight t)
  have he : ∀ b0 : ZMod M, e b0 = cwQ6DoubledZHash b0 w z := by
    intro b0
    simp [e, t, cwQ6DoubledZHash]
  have hfilter :
      (Finset.univ : Finset (ZMod M)).filter (fun b0 =>
          ∃ s ∈ S,
            cwQ6DoubledZHash b0 w z = 2 * (s : ZMod M)) =
        T.map e.symm.toEmbedding := by
    ext b0
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_map]
    constructor
    · rintro ⟨s, hs, hlabel⟩
      refine ⟨2 * (s : ZMod M), ?_, ?_⟩
      · exact Finset.mem_image.mpr ⟨s, hs, rfl⟩
      · change e.symm (2 * (s : ZMod M)) = b0
        rw [e.symm_apply_eq, he]
        exact hlabel.symm
    · rintro ⟨r, hr, hrb⟩
      obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hr
      refine ⟨s, hs, ?_⟩
      change e.symm (2 * (s : ZMod M)) = b0 at hrb
      rw [← he]
      have h := congrArg e hrb
      simpa using h.symm
  rw [hfilter, Finset.card_map, hTcard]
