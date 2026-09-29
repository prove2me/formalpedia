-- Prove2me | solution 1 for mme_dwz_fine_z_owner_exists_of_unique_compatibility
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-25T20:07:17.65883+00:00
-- url     : https://prove2.me/submissions/9362c8d5-ad4a-494a-8dc0-4009d0b856ac

import Definitions.Def_mme_induced_word_zeroing

open MME

universe u

set_option autoImplicit false
set_option warningAsError true

theorem solution
    {K : Type u} [Field K]
    {T : TensorObj K 3} {t N k : ℕ}
    (G : T.TypeGrading t)
    (fineAddress : Fin k → Fin 3 → Fin N → Fin t)
    (compatible : (Fin N → Fin t) → Fin k → Prop)
    [DecidableRel compatible]
    (hTargetCompatible : ∀ j : Fin k,
      compatible (fineAddress j 2) j)
    (hTargetUnique : ∀ j j' : Fin k,
      compatible (fineAddress j 2) j' → j' = j)
    (hSupportedCompatible : ∀ js : Fin 3 → Fin k,
      (∀ r : Fin N,
        G.blockTensor (fun i ↦ fineAddress (js i) i r) ≠ 0) →
      compatible (fineAddress (js 2) 2) (js 0)) :
    ∃ fineZOwner : (Fin N → Fin t) → Option (Fin k),
      (∀ z,
        fineZOwner z = none ↔ ¬ ∃! j, compatible z j) ∧
      (∀ z j,
        fineZOwner z = some j ↔
          compatible z j ∧
            ∀ j', compatible z j' → j' = j) ∧
      (∀ j : Fin k,
        fineZOwner (fineAddress j 2) = some j) ∧
      (∀ js : Fin 3 → Fin k,
        (∀ r : Fin N,
          G.blockTensor (fun i ↦ fineAddress (js i) i r) ≠ 0) →
        fineZOwner (fineAddress (js 2) 2) = some (js 0)) := by
  let uniqueCompatibleDecidable (z : Fin N → Fin t) :
      Decidable (∃! j, compatible z j) := by
    apply Fintype.decidableExistsFintype
  let fineZOwner : (Fin N → Fin t) → Option (Fin k) := fun z ↦
    if h : ∃! j, compatible z j then
      some (Classical.choose h)
    else
      none
  have hNone : ∀ z,
      fineZOwner z = none ↔ ¬ ∃! j, compatible z j := by
    intro z
    by_cases h : ∃! j, compatible z j
    · simp [fineZOwner, h]
    · simp [fineZOwner, h]
  have hSome : ∀ z j,
      fineZOwner z = some j ↔
        compatible z j ∧ ∀ j', compatible z j' → j' = j := by
    intro z j
    by_cases h : ∃! j, compatible z j
    · rw [show fineZOwner z = some (Classical.choose h) by
        simp [fineZOwner, h]]
      constructor
      · intro hj
        have hEq : Classical.choose h = j := Option.some.inj hj
        simpa [hEq] using (Classical.choose_spec h)
      · intro hj
        have hEq : Classical.choose h = j :=
          hj.2 (Classical.choose h) (Classical.choose_spec h).1
        exact congrArg some hEq
    · constructor
      · intro hImpossible
        simp [fineZOwner, h] at hImpossible
      · intro hj
        exfalso
        apply h
        exact ⟨j, hj.1, hj.2⟩
  have hOwned : ∀ j : Fin k,
      fineZOwner (fineAddress j 2) = some j := by
    intro j
    exact (hSome (fineAddress j 2) j).2
      ⟨hTargetCompatible j, hTargetUnique j⟩
  have hSupportedOwner : ∀ js : Fin 3 → Fin k,
      (∀ r : Fin N,
        G.blockTensor (fun i ↦ fineAddress (js i) i r) ≠ 0) →
      fineZOwner (fineAddress (js 2) 2) = some (js 0) := by
    intro js hsupported
    have hCompatible :
        compatible (fineAddress (js 2) 2) (js 0) :=
      hSupportedCompatible js hsupported
    apply (hSome (fineAddress (js 2) 2) (js 0)).2
    refine ⟨hCompatible, ?_⟩
    intro j' hj'
    have hj'Target : j' = js 2 := hTargetUnique (js 2) j' hj'
    have hXTarget : js 0 = js 2 :=
      hTargetUnique (js 2) (js 0) hCompatible
    exact hj'Target.trans hXTarget.symm
  exact ⟨fineZOwner, hNone, hSome, hOwned, hSupportedOwner⟩
