-- Prove2me | solution 1 for gpy_mem_localGoodChoiceFinset
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-10-31T02:22:17.069072+00:00
-- url     : https://prove2.me/submissions/d99e87d8-8681-4f14-96c8-7c3d8dcc3b3a

import Mathlib

open scoped BigOperators
open Classical

set_option autoImplicit false

noncomputable def localGoodChoiceFinset {k : ℕ} (h : Fin k → ℕ) (i : Fin k)
    (p : ℕ) (hd he : Prop) [Decidable hd] [Decidable he] :
    Finset (Option (Fin k) × Option (Fin k)) :=
  Finset.univ.filter (fun ab =>
    (ab.1.isSome ↔ hd) ∧ (ab.2.isSome ↔ he) ∧
    (∀ j j', (ab.1 = some j ∨ ab.2 = some j) →
      (ab.1 = some j' ∨ ab.2 = some j') → h j ≡ h j' [MOD p]) ∧
    (∀ j, (ab.1 = some j ∨ ab.2 = some j) → ¬ h i ≡ h j [MOD p]))

theorem mem_localGoodChoiceFinset_aux {k : ℕ} {h : Fin k → ℕ} {i : Fin k} {p : ℕ}
    {hd he : Prop} [Decidable hd] [Decidable he]
    {ab : Option (Fin k) × Option (Fin k)} :
    ab ∈ localGoodChoiceFinset h i p hd he ↔
      (ab.1.isSome ↔ hd) ∧ (ab.2.isSome ↔ he) ∧
      (∀ j j', (ab.1 = some j ∨ ab.2 = some j) →
        (ab.1 = some j' ∨ ab.2 = some j') → h j ≡ h j' [MOD p]) ∧
      (∀ j, (ab.1 = some j ∨ ab.2 = some j) → ¬ h i ≡ h j [MOD p]) := by
  simp only [localGoodChoiceFinset, Finset.mem_filter, Finset.mem_univ, true_and]

theorem solution {k : ℕ} {h : Fin k → ℕ} {i : Fin k}
    {p : ℕ} {hd he : Prop} [Decidable hd] [Decidable he]
    {ab : Option (Fin k) × Option (Fin k)} :
    ab ∈ (Finset.univ : Finset (Option (Fin k) × Option (Fin k))).filter (fun ab =>
      (ab.1.isSome ↔ hd) ∧ (ab.2.isSome ↔ he) ∧
      (∀ j j', (ab.1 = some j ∨ ab.2 = some j) →
        (ab.1 = some j' ∨ ab.2 = some j') → h j ≡ h j' [MOD p]) ∧
      (∀ j, (ab.1 = some j ∨ ab.2 = some j) → ¬ h i ≡ h j [MOD p])) ↔
      (ab.1.isSome ↔ hd) ∧ (ab.2.isSome ↔ he) ∧
      (∀ j j', (ab.1 = some j ∨ ab.2 = some j) →
        (ab.1 = some j' ∨ ab.2 = some j') → h j ≡ h j' [MOD p]) ∧
      (∀ j, (ab.1 = some j ∨ ab.2 = some j) → ¬ h i ≡ h j [MOD p]) :=
  mem_localGoodChoiceFinset_aux
