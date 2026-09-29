-- Prove2me | solution 1 for mme_CW_q6_difference_code_has_unit_coefficient
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-24T22:25:18.598915+00:00
-- url     : https://prove2.me/submissions/db362561-32bc-4849-bfd4-1c2b8d415a72

import Mathlib
import Definitions.Def_mme_CW_q6_doubled_hash_arithmetic

open MME

set_option autoImplicit false

/-- A positive q=6 middle profile makes every X-minus-Z coefficient word
contain a unit entry. -/
theorem solution
    {M N L G : ℕ} [NeZero M]
    (e : CWQ6ExactCoupledAddress N L G)
    (hG : 0 < G) :
    ∃ j : Fin (2 * N), IsUnit (
      (2 * ((e.1 0 j).val : ZMod M)) -
        (cwQ6CoupledZHashCode (e.1 2 j) : ZMod M)) := by
  have hcard := e.2.2 (2 : Fin 3) (2 : Fin 3)
  have hmultiplicity :
      cwQ6CoupledMarginalMultiplicity N L G (2 : Fin 3) (2 : Fin 3) =
        2 * G := by
    norm_num [cwQ6CoupledMarginalMultiplicity, Fin.ext_iff]
  have hpos : 0 <
      (Finset.univ.filter (fun j : Fin (2 * N) => e.1 2 j = 2)).card := by
    rw [hcard, hmultiplicity]
    omega
  obtain ⟨j, hj⟩ := Finset.card_pos.mp hpos
  have hz : e.1 2 j = 2 := (Finset.mem_filter.mp hj).2
  refine ⟨j, ?_⟩
  rcases e.2.1 j with h0 | h1 | h2 | h3
  · rcases h0 with ⟨_hx, _hy, hz'⟩
    omega
  · rcases h1 with ⟨_hx, _hy, hz'⟩
    omega
  · rcases h2 with ⟨hx, _hy, hz'⟩
    simpa [hx, hz', cwQ6CoupledZHashCode] using
      (isUnit_neg_one : IsUnit (-1 : ZMod M))
  · rcases h3 with ⟨hx, _hy, hz'⟩
    convert (isUnit_one : IsUnit (1 : ZMod M)) using 1 <;>
      simp [hx, hz', cwQ6CoupledZHashCode] <;> ring
