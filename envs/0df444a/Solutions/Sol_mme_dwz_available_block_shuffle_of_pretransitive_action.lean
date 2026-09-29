-- Prove2me | solution 1 for mme_dwz_available_block_shuffle_of_pretransitive_action
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-26T07:25:17.540923+00:00
-- url     : https://prove2.me/submissions/46dc660b-6593-4027-ae41-3513d09e83ea

import Definitions.Def_mme_dwz_hole_cover_data
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.GroupAction.Transitive

set_option autoImplicit false
set_option warningAsError true

open Finset
open MME.DWZSquare

universe u v

theorem solution
    (Block : Type u) (G : Type v)
    [Fintype Block] [DecidableEq Block]
    [Group G] [Fintype G] [DecidableEq G]
    [MulAction G Block] [MulAction.IsPretransitive G Block] :
    ∃ system : AvailableBlockShuffle Block G,
      ∀ g source, system.move g source = g • source := by
  classical
  have uniform : ∀ source target : Block,
      (univ.filter (fun g : G => (MulAction.toPerm g) source = target)).card *
          Fintype.card Block =
        Fintype.card G := by
    intro source target
    obtain ⟨h, hh⟩ := MulAction.exists_smul_eq G source target
    let fiberEquiv :
        {g : G // g • source = target} ≃ MulAction.stabilizer G source :=
      { toFun := fun g => ⟨h⁻¹ * g.1, by
          change (h⁻¹ * g.1) • source = source
          rw [mul_smul, g.2, ← hh, inv_smul_smul]⟩
        invFun := fun k => ⟨h * k.1, by
          rw [mul_smul, k.2, hh]⟩
        left_inv := fun g => by
          apply Subtype.ext
          simp
        right_inv := fun k => by
          apply Subtype.ext
          simp }
    have hfiber :
        (univ.filter (fun g : G => g • source = target)).card =
          Fintype.card (MulAction.stabilizer G source) := by
      rw [← Fintype.card_subtype]
      exact Fintype.card_congr fiberEquiv
    have horbit :
        Fintype.card (MulAction.orbit G source) = Fintype.card Block := by
      rw [MulAction.orbit_eq_univ]
      simp
    have horbitStabilizer :=
      MulAction.card_orbit_mul_card_stabilizer_eq_card_group G source
    rw [horbit] at horbitStabilizer
    change (univ.filter (fun g : G => g • source = target)).card *
        Fintype.card Block = Fintype.card G
    rw [hfiber]
    simpa [Nat.mul_comm] using horbitStabilizer
  let system : AvailableBlockShuffle Block G :=
    { move := MulAction.toPerm
      uniform_fiber := uniform }
  refine ⟨system, ?_⟩
  intro g source
  exact MulAction.toPerm_apply g source
