-- Prove2me | solution 1 for gpy_localGoodChoiceFinset_card_congr
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-11-01T02:53:32.180517+00:00
-- url     : https://prove2.me/submissions/0724ca83-a8ed-4f63-8754-6d7109f88fd3

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

theorem localGoodChoiceFinset_card_congr_aux {k : ℕ} {h : Fin k → ℕ} {i : Fin k}
    {p : ℕ} {hd he hd' he' : Prop} [Decidable hd] [Decidable he]
    [Decidable hd'] [Decidable he'] (h1 : hd ↔ hd') (h2 : he ↔ he') :
    (localGoodChoiceFinset h i p hd he).card
      = (localGoodChoiceFinset h i p hd' he').card := by
  unfold localGoodChoiceFinset
  congr 1
  apply Finset.filter_congr
  intro ab _
  simp only [h1, h2]

theorem solution {k : ℕ} {h : Fin k → ℕ} {i : Fin k}
    {p : ℕ} {hd he hd' he' : Prop} [Decidable hd] [Decidable he]
    [Decidable hd'] [Decidable he'] (h1 : hd ↔ hd') (h2 : he ↔ he') :
    ((Finset.univ : Finset (Option (Fin k) × Option (Fin k))).filter (fun ab =>
      (ab.1.isSome ↔ hd) ∧ (ab.2.isSome ↔ he) ∧
      (∀ j j', (ab.1 = some j ∨ ab.2 = some j) →
        (ab.1 = some j' ∨ ab.2 = some j') → h j ≡ h j' [MOD p]) ∧
      (∀ j, (ab.1 = some j ∨ ab.2 = some j) → ¬ h i ≡ h j [MOD p]))).card
      = ((Finset.univ : Finset (Option (Fin k) × Option (Fin k))).filter (fun ab =>
      (ab.1.isSome ↔ hd') ∧ (ab.2.isSome ↔ he') ∧
      (∀ j j', (ab.1 = some j ∨ ab.2 = some j) →
        (ab.1 = some j' ∨ ab.2 = some j') → h j ≡ h j' [MOD p]) ∧
      (∀ j, (ab.1 = some j ∨ ab.2 = some j) → ¬ h i ≡ h j [MOD p]))).card :=
  localGoodChoiceFinset_card_congr_aux h1 h2
