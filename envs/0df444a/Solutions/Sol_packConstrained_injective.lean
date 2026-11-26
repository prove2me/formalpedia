-- Prove2me | solution 1 for packConstrained_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T22:46:35.334606+00:00
-- url     : https://prove2.me/submissions/6bfe184b-c077-4943-8d40-81eeb9aa7974

import Definitions.Def_CARDB
import Mathlib.Data.Fintype.Prod
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Definitions.Def_CARDB_Asymptotics

set_option autoImplicit true
open Set TopologicalSpace
variable {α : Type*} [Fintype α] [DecidableEq α]
variable {x y : α}
theorem _root_.solution (a b : α) (hne : a ≠ b) :
    Function.Injective (packConstrained a b hne) := by
  classical
  intro U V h
  apply Subtype.ext
  have hrest := congrArg Prod.fst h
  have hstat := congrArg Prod.snd h
  ext z
  by_cases hza : z = a
  · rw [hza]
    have : (if a ∈ U.1 then (⟨2, by decide⟩ : Fin 3) else if b ∈ U.1 then ⟨1, by decide⟩ else ⟨0, by decide⟩) =
        (if a ∈ V.1 then ⟨2, by decide⟩ else if b ∈ V.1 then ⟨1, by decide⟩ else ⟨0, by decide⟩) := by
      simpa [packConstrained] using hstat
    split_ifs at this <;> simp_all
  · by_cases hzb : z = b
    · rw [hzb]
      have : (if a ∈ U.1 then (⟨2, by decide⟩ : Fin 3) else if b ∈ U.1 then ⟨1, by decide⟩ else ⟨0, by decide⟩) =
          (if a ∈ V.1 then ⟨2, by decide⟩ else if b ∈ V.1 then ⟨1, by decide⟩ else ⟨0, by decide⟩) := by
        simpa [packConstrained] using hstat
      split_ifs at this <;> try simp_all
      · exact iff_of_true (U.2 (by simp_all)) (V.2 (by simp_all))
    · have := Set.ext_iff.mp hrest ⟨z, ⟨hza, hzb⟩⟩
      simpa [packConstrained] using this
